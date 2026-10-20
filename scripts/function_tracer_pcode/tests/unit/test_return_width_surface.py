import pytest
import hashlib
from dataclasses import replace
from types import SimpleNamespace
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer

from scripts.function_tracer_pcode.proof.obligations.return_width import prove_function_return_width
from scripts.function_tracer_pcode.proof.return_width.pipeline import (
    prepare_function_return_widths,
    prepare_pair_return_observation,
    return_coverage_artifact_ids,
    _width_completion_evidence,
)
from scripts.function_tracer_pcode.proof.return_width.surface import (
    BlockedObservation,
    CorrespondenceValidationStatus,
    build_observation_view,
    build_top_level_observation_contract,
    extract_function_return_width_seed,
    build_input_correspondence_contract,
    build_call_site_return_width_receipt,
    prove_object_query_input_correspondence,
    _declared_observation_width,
)
from scripts.function_tracer_pcode.proof.call_effect.preflight import QueryExecutionRecord
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    build_canonical_return_observation_query,
    extract_return_cases,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    _build_model_validation_query,
)
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    ComparisonSurface,
    Expression,
    FunctionReturnAnalysis,
    PcodeOpRef,
    ReturnInfo,
    ReturnValueFlowCertificate,
    ReturnValueFlowStep,
    VarnodeFlowRef,
)
from scripts.function_tracer_pcode.core.structural import value_identity
import scripts.function_tracer_pcode.proof.strategies.monolithic_return_width as _mx_monolithic_return_width
from scripts.function_tracer_pcode.proof.formula.input_correspondence import build_input_correspondence_set


def _analysis(binary_id, entry, storage_bits, *, extension=None):
    value = Expression.parameter("value", 0, data_type="int", size=4)
    refs = ()
    return_ref = PcodeOpRef(
        address_offset=entry + 0x20,
        seq_time=2,
        seq_order=0,
        mnemonic="RETURN",
        input_sizes=(8, storage_bits // 8),
        binary_id=binary_id,
        function_entry_offset=entry,
        target_offset=entry + 0x20,
    )
    certificate = None
    if extension is not None:
        extension_ref = PcodeOpRef(
                binary_id=binary_id,
                function_entry_offset=entry,
                target_offset=entry + 0x10,
                seq_time=1,
                seq_order=0,
                mnemonic=extension,
                input_sizes=(4,),
                output_size=storage_bits // 8,
            )
        refs = (extension_ref,)
        payload_ref = VarnodeFlowRef(1, "unique", entry + 1, 4)
        storage_ref = VarnodeFlowRef(1, "unique", entry + 2, storage_bits // 8)
        certificate = ReturnValueFlowCertificate(
            return_op_ref=return_ref,
            return_input_index=1,
            return_input_ref=storage_ref,
            steps=(ReturnValueFlowStep(
                op_ref=extension_ref,
                output_ref=storage_ref,
                input_refs=(payload_ref,),
                traversed_input_index=0,
            ),),
            extension_step_index=0,
            payload_expression_identity=tuple(value_identity(value)),
        )
    analysis = FunctionReturnAnalysis(
        function_name="f",
        entry_point=hex(entry),
        parameters=[],
        returns=[
            ReturnInfo(
                address=hex(entry + 0x10),
                value=value,
                pcode_op_ref=return_ref,
                return_value_pcode_op_refs=refs,
                return_value_flow_certificate=certificate,
            )
        ],
        function_ref=CallTargetRef.from_name(
            "f", program_id=entry, entry_offset=entry
        ),
        return_type="int",
        comparison_surface=ComparisonSurface(
            kind="return_value",
            explicit_bit_width=storage_bits,
            type_name="int" if storage_bits == 32 else "long",
        ),
        return_type_provenance={
            "object_derived": True,
            "declared_return_type_width": 32,
        },
        binary_id=binary_id,
    )
    return analysis


def test_function_width_target_and_seed_are_pair_independent():
    analysis = _analysis("B1", 0x1000, 64, extension="INT_SEXT")
    case = extract_return_cases(analysis)[0]

    seed = extract_function_return_width_seed(analysis, case)

    assert seed.complete
    assert seed.storage_width == 64
    assert seed.payload_width == 32
    assert seed.extension_evidence_source.kind == "sign_extend"
    assert "left" not in repr(seed.stable_key())
    assert "pair_id" not in repr(seed.stable_key())


def test_extension_certificate_input_defines_semantic_payload_width_and_identity():
    analysis = _analysis("B-real-extension", 0x1800, 64, extension="INT_ZEXT")
    payload = analysis.returns[0].value
    extended = Expression.unary_op("INT_ZEXT", payload)
    extended.size = 8
    analysis.returns[0].value = extended
    certificate = analysis.returns[0].return_value_flow_certificate
    analysis.returns[0].return_value_flow_certificate = ReturnValueFlowCertificate(
        return_op_ref=certificate.return_op_ref,
        return_input_index=certificate.return_input_index,
        return_input_ref=certificate.return_input_ref,
        steps=certificate.steps,
        extension_step_index=certificate.extension_step_index,
        payload_expression_identity=tuple(value_identity(payload)),
    )

    seed = extract_function_return_width_seed(
        analysis, extract_return_cases(analysis)[0]
    )

    assert seed.complete
    assert seed.storage_width == 64
    assert seed.payload_width == 32
    assert seed.payload_value_identity == tuple(value_identity(payload))
    assert seed.extension_evidence_source.kind == "zero_extend"

    proof = prove_function_return_width(analysis, seed)
    assert _width_completion_evidence(proof)["width_facts"] == {
        "storage_width": 64,
        "semantic_payload_width": 32,
        "declared_observation_width": 32,
        "extension_kind": "zero_extend",
        "extension_flow_kind": "certified_return_input_def_chain",
    }


def _observation_seed(binary_id, entry, provenance, *, storage_bits=64):
    """Build one unary width seed whose return_type_provenance is fully controlled."""
    analysis = _analysis(binary_id, entry, storage_bits, extension="INT_SEXT")
    analysis.return_type_provenance = dict(provenance)
    return extract_function_return_width_seed(
        analysis, extract_return_cases(analysis)[0]
    )


_DECOMPILER_DECLARED_PROVENANCE = {
    "object_derived": True,
    "return_type": "int",
    "return_type_source": "decompiler_return_type",
    "declared_return_type_width": 32,
}

_UNDECLARED_PROVENANCE = {
    "object_derived": True,
    "return_type": "undefined8",
    "return_type_source": "undefined_decompiler_type",
    "declared_return_type_width": None,
}


def test_declared_observation_width_ignores_source_declared_entries():
    """Issue #122: 観測幅は Ghidra prototype 由来の宣言幅のみを見る。"""
    fact = (
        "return_type_provenance",
        (
            ("declared_return_type_width", 64),
            ("source_declared_return_type_known", True),
            ("source_declared_return_type_width", 32),
        ),
    )

    assert _declared_observation_width(fact) == 64


def test_top_level_observation_contract_names_the_decompiler_declared_derivation():
    """Issue #122: 宣言幅由来の contract は source ではなく decompiler 由来を名乗る。"""
    left = _observation_seed("B-decl-left", 0x3000, _DECOMPILER_DECLARED_PROVENANCE)
    right = _observation_seed("B-decl-right", 0x4000, _DECOMPILER_DECLARED_PROVENANCE)

    contract = build_top_level_observation_contract(left, right)

    assert not isinstance(contract, BlockedObservation)
    assert contract.observation_semantics == (
        "return_value",
        "decompiler_declared_return_width",
    )
    assert contract.projection_policy == "abi_declared_return_width_v1"
    assert contract.left_observation_width == 32
    assert contract.right_observation_width == 32
    assert "source_declared" not in repr(contract.provenance)
    assert "source_declared" not in repr(contract.observation_semantics)


def test_observation_contract_keeps_binary_only_common_payload_width_fallback():
    """Issue #122: 宣言幅が無くても binary-only の共通 payload 幅で contract は成立する。"""
    left = _observation_seed("B-fallback-left", 0x5000, _UNDECLARED_PROVENANCE)
    right = _observation_seed("B-fallback-right", 0x6000, _UNDECLARED_PROVENANCE)

    assert left.extension_evidence_source.supported
    assert right.extension_evidence_source.supported

    contract = build_top_level_observation_contract(left, right)

    assert not isinstance(contract, BlockedObservation)
    assert contract.observation_semantics == (
        "return_value",
        "common_validated_semantic_payload_width",
    )
    assert contract.projection_policy == "validated_semantic_payload_width_v1"
    assert contract.left_observation_width == 32


def test_observation_contract_fails_closed_on_incompatible_payload_widths():
    """Issue #122 / AC3: 幅が食い違えば pair 契約の不足として Blocked。"""
    left = _observation_seed("B-mismatch-left", 0x7000, _UNDECLARED_PROVENANCE)
    right = replace(
        _observation_seed("B-mismatch-right", 0x8000, _UNDECLARED_PROVENANCE),
        payload_width=64,
    )

    blocked = build_top_level_observation_contract(left, right)

    assert isinstance(blocked, BlockedObservation)
    assert [
        (blocker.blocker_kind, blocker.missing_slot) for blocker in blocked.blockers
    ] == [("observation_contract", "top_level_comparison_contract")]


def test_observation_contract_fails_closed_on_unknown_payload_width():
    """Issue #122 / AC3: payload 幅そのものが未解決なら unary 側の不足として Blocked。"""
    left = _observation_seed("B-nopayload-left", 0x9000, _UNDECLARED_PROVENANCE)
    right = replace(
        _observation_seed("B-nopayload-right", 0xA000, _UNDECLARED_PROVENANCE),
        payload_width=None,
        unresolved_fact_slots=("payload_width_fact",),
    )

    blocked = build_top_level_observation_contract(left, right)

    assert isinstance(blocked, BlockedObservation)
    assert [
        (blocker.blocker_kind, blocker.missing_slot) for blocker in blocked.blockers
    ] == [("unary_width", "payload_width_fact")]


def test_observation_contract_fails_closed_without_extension_evidence():
    """Issue #122 / AC3: 拡張証拠が無ければ unary 側の不足として Blocked。"""
    left = _observation_seed("B-noext-left", 0xB000, _UNDECLARED_PROVENANCE)
    right_seed = _observation_seed("B-noext-right", 0xC000, _UNDECLARED_PROVENANCE)
    right = replace(
        right_seed,
        extension_evidence_source=replace(
            right_seed.extension_evidence_source, kind="unsupported"
        ),
        unresolved_fact_slots=("extension_evidence_fact",),
    )

    blocked = build_top_level_observation_contract(left, right)

    assert isinstance(blocked, BlockedObservation)
    assert [
        (blocker.blocker_kind, blocker.missing_slot) for blocker in blocked.blockers
    ] == [("unary_width", "extension_evidence_fact")]


def test_unary_width_artifact_is_domain_cached_and_pair_independent():
    analysis = _analysis("B2", 0x2000, 64, extension="INT_ZEXT")
    seed = extract_function_return_width_seed(analysis, extract_return_cases(analysis)[0])

    first = prove_function_return_width(analysis, seed)
    second = prove_function_return_width(analysis, seed)

    assert first.complete
    assert second.complete
    assert second.cache_hit
    assert first.validated_artifact.artifact_id == second.validated_artifact.artifact_id


def test_observation_view_fails_closed_without_validated_return_coverage():
    left = _analysis("B3", 0x3000, 32)
    right = _analysis("B4", 0x4000, 64, extension="INT_SEXT")
    left_seed = extract_function_return_width_seed(left, extract_return_cases(left)[0])
    right_seed = extract_function_return_width_seed(right, extract_return_cases(right)[0])
    left_proof = prove_function_return_width(left, left_seed).validated_artifact
    right_proof = prove_function_return_width(right, right_seed).validated_artifact
    contract = build_top_level_observation_contract(left_seed, right_seed)

    result = build_observation_view(
        contract,
        left_proof,
        right_proof,
        validated_closure_id=("closure",),
        return_coverage_artifact_ids=(("coverage",),),
    )

    assert isinstance(result, BlockedObservation)
    assert result.blockers[0].missing_slot == "return_coverage_artifact_ids"


def test_pipeline_builds_proven_view_and_trivial_binding_receipt():
    left = _analysis("B5", 0x5000, 32)
    right = _analysis("B6", 0x6000, 64, extension="INT_SEXT")
    left_cases = extract_return_cases(left)
    right_cases = extract_return_cases(right)
    stats = {}
    left_prepared = prepare_function_return_widths(left, left_cases, stats)
    right_prepared = prepare_function_return_widths(right, right_cases, stats)

    result = prepare_pair_return_observation(
        left,
        right,
        left_cases[0],
        right_cases[0],
        left_prepared,
        right_prepared,
        return_coverage_ids=(("validated-return-coverage",),),
        proof_runtime=SimpleNamespace(artifacts=(SimpleNamespace(
            artifact_id=("validated-return-coverage",),
            is_validated=True,
            premise_digest="coverage-premise",
            payload={"proof": "coverage"},
        ),)),
        stats=stats,
    )

    assert result.proven
    assert result.view.canonical_comparison_width == 32
    assert result.binding_receipt.correspondence_validation_status == (
        CorrespondenceValidationStatus.TRIVIAL_OBJECT_CORRESPONDENCE.value
    )
    assert result.binding_receipt.binding_proof_artifact_ids == ()
    assert stats["width_observation_proven"] == 1


def test_top_level_contract_can_use_common_proven_semantic_payload_width():
    left = _analysis("B-payload-left", 0x6100, 32)
    right = _analysis("B-payload-right", 0x6200, 64, extension="INT_SEXT")
    left.return_type_provenance = {"object_derived": True}
    right.return_type_provenance = {"object_derived": True}
    left_seed = extract_function_return_width_seed(left, extract_return_cases(left)[0])
    right_seed = extract_function_return_width_seed(right, extract_return_cases(right)[0])

    contract = build_top_level_observation_contract(left_seed, right_seed)

    assert not isinstance(contract, BlockedObservation)
    assert contract.left_observation_width == 32
    assert contract.right_observation_width == 32
    assert contract.observation_semantics == (
        "return_value",
        "common_validated_semantic_payload_width",
    )


def test_unsupported_implicit_width_change_remains_blocked():
    analysis = _analysis("B7", 0x7000, 64)
    seed = extract_function_return_width_seed(analysis, extract_return_cases(analysis)[0])

    result = prove_function_return_width(analysis, seed)

    assert not seed.complete
    assert result.status == "blocked"
    assert result.blocker_kind == "return_width_seed_incomplete"


def test_detached_extension_ref_cannot_prove_return_storage_relation():
    analysis = _analysis("B-detached", 0x7100, 64, extension="INT_SEXT")
    info = analysis.returns[0]
    info.return_value_flow_certificate = None

    seed = extract_function_return_width_seed(analysis, extract_return_cases(analysis)[0])
    result = prove_function_return_width(analysis, seed)

    assert not seed.complete
    assert seed.extension_evidence_source.kind == "unsupported"
    assert result.status == "blocked"


def test_high_bit_near_miss_with_wrong_extension_output_is_blocked():
    analysis = _analysis("B-near", 0x7200, 64, extension="INT_SEXT")
    certificate = analysis.returns[0].return_value_flow_certificate
    wrong_step = ReturnValueFlowStep(
        op_ref=PcodeOpRef(
            address_offset=0x7210,
            mnemonic="INT_SEXT",
            input_sizes=(4,),
            output_size=4,
        ),
        output_ref=certificate.steps[0].output_ref,
        input_refs=certificate.steps[0].input_refs,
        traversed_input_index=0,
    )
    analysis.returns[0].return_value_flow_certificate = ReturnValueFlowCertificate(
        return_op_ref=certificate.return_op_ref,
        return_input_index=1,
        return_input_ref=certificate.return_input_ref,
        steps=(wrong_step,),
        extension_step_index=0,
        payload_expression_identity=certificate.payload_expression_identity,
    )

    seed = extract_function_return_width_seed(analysis, extract_return_cases(analysis)[0])

    assert not seed.complete
    assert seed.extension_evidence_source.kind == "unsupported"


def test_analyzer_builds_certificate_only_from_actual_return_input_def_chain():
    class _Space:
        def getSpaceID(self):
            return 1

        def getName(self):
            return "unique"

    class _Address:
        def getAddressSpace(self):
            return _Space()

    class _Varnode:
        def __init__(self, offset, size, definition=None):
            self.offset = offset
            self.size = size
            self.definition = definition

        def getAddress(self):
            return _Address()

        def getOffset(self):
            return self.offset

        def getSize(self):
            return self.size

        def getDef(self):
            return self.definition

    class _Op:
        def __init__(self, mnemonic, inputs, output=None):
            self.mnemonic = mnemonic
            self.inputs = list(inputs)
            self.output = output

        def getMnemonic(self):
            return self.mnemonic

        def getNumInputs(self):
            return len(self.inputs)

        def getInput(self, index):
            return self.inputs[index]

        def getOutput(self):
            return self.output

        def getOpcode(self):
            return None

        def getSeqnum(self):
            return None

        def getParent(self):
            return None

    payload = _Varnode(0x10, 4)
    storage = _Varnode(0x20, 8)
    extension = _Op("INT_SEXT", [payload], storage)
    storage.definition = extension
    return_op = _Op("RETURN", [_Varnode(0, 8), storage])
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer._binary_id = "B-object-flow"
    return_ref = PcodeOpRef.from_pcode_op(return_op, binary_id=analyzer._binary_id)
    tracer = Mock()
    tracer.trace_varnode.return_value = Expression.parameter(
        "value", 0, data_type="int", size=4
    )

    metadata = analyzer._site_metadata_with_return_value_pcode_op_refs(
        {"_return_op_object": return_op, "pcode_op_ref": return_ref},
        return_varnode=storage,
        producer_op=extension,
        tracer=tracer,
    )
    certificate = metadata["return_value_flow_certificate"]

    assert certificate.return_input_ref.size == 8
    assert certificate.extension_step_index == 0
    assert certificate.steps[0].output_ref == certificate.return_input_ref
    assert certificate.steps[0].input_refs[0].size == 4

    detached = _Varnode(0x30, 8, extension)
    detached_metadata = analyzer._site_metadata_with_return_value_pcode_op_refs(
        {"_return_op_object": return_op, "pcode_op_ref": return_ref},
        return_varnode=detached,
        producer_op=extension,
        tracer=tracer,
    )
    assert "return_value_flow_certificate" not in detached_metadata


def test_call_site_receipt_requires_exact_return_proof_and_width_contract():
    left = Expression.parameter("left", 0, size=8)
    right = Expression.parameter("right", 0, size=4)
    binding = SimpleNamespace(
        binding_id="binding-1",
        proof_stage_records=(("return_relation", "proof-id", "query-digest"),),
        return_width_relation_contract=(
            ("narrow_bits", 32),
            ("wide_bits", 64),
            ("wide_side", "left"),
            ("extension", "sign_extend"),
            ("proof_basis", ("validated-return-relation",)),
        ),
    )

    receipt = build_call_site_return_width_receipt(
        binding=binding,
        pair_id="(0,0)",
        left_expr=left,
        right_expr=right,
        lowered_left_term="left_1",
        lowered_right_term="right_2",
    )

    assert not isinstance(receipt, BlockedObservation)
    assert receipt.observation_width == 32
    assert receipt.return_relation_proof_records == (
        ("return_relation", "proof-id", "query-digest"),
    )
    assert receipt.projection_direction == "left_to_low_bits"
    assert receipt.left_projection_range == (31, 0)
    assert receipt.projected_left_term == "((_ extract 31 0) left_1)"
    assert receipt.assertion_text == (
        "(assert (= ((_ extract 31 0) left_1) right_2))"
    )

    binding.return_width_relation_contract = (
        ("narrow_bits", 32),
        ("wide_bits", 64),
        ("wide_side", "right"),
        ("extension", "sign_extend"),
        ("proof_basis", ("validated-return-relation",)),
    )
    assert isinstance(build_call_site_return_width_receipt(
        binding=binding,
        pair_id="(0,0)",
        left_expr=left,
        right_expr=right,
        lowered_left_term="left_1",
        lowered_right_term="right_2",
    ), BlockedObservation)

    binding.return_width_relation_contract = (
        ("narrow_bits", 32),
        ("wide_bits", 64),
        ("extension", "sign_extend"),
    )
    assert isinstance(build_call_site_return_width_receipt(
        binding=binding,
        pair_id="(0,0)",
        left_expr=left,
        right_expr=right,
        lowered_left_term="left_1",
        lowered_right_term="right_2",
    ), BlockedObservation)


def test_query_execution_record_rejects_missing_call_site_receipt_marker():
    digest = "a" * 64
    assertion = "(assert (= ((_ extract 31 0) left_1) right_2))"
    assertion_digest = hashlib.sha256(assertion.encode("utf-8")).hexdigest()
    formula = (
        f"(set-logic QF_BV)\n; call_site_return_width_receipt {digest} "
        f"assertion_sha256={assertion_digest}\n{assertion}\n(check-sat)"
    )
    formula_digest = hashlib.sha256(formula.encode("utf-8")).hexdigest()
    record = QueryExecutionRecord(
        query_label="pair-(0,0)",
        premise_digest="b" * 64,
        formula_digest=formula_digest,
        disposition="unsat",
        proof_kind="pairwise_solver_query",
        formula_text=formula,
        call_site_return_width_receipt_digests=(digest,),
        call_site_return_width_receipt_assertion_digests=(
            (digest, assertion_digest),
        ),
    )

    assert record.validate()
    assert not QueryExecutionRecord(
        query_label=record.query_label,
        premise_digest=record.premise_digest,
        formula_digest=hashlib.sha256("(check-sat)".encode("utf-8")).hexdigest(),
        disposition=record.disposition,
        proof_kind=record.proof_kind,
        formula_text="(check-sat)",
        call_site_return_width_receipt_digests=(digest,),
        call_site_return_width_receipt_assertion_digests=(
            (digest, assertion_digest),
        ),
    ).validate()


def test_query_execution_record_rejects_call_site_assertion_or_projection_mutation():
    digest = "a" * 64
    assertion = "(assert (= ((_ extract 31 0) left_1) right_2))"
    assertion_digest = hashlib.sha256(assertion.encode("utf-8")).hexdigest()
    marker = (
        f"; call_site_return_width_receipt {digest} "
        f"assertion_sha256={assertion_digest}"
    )

    for replacement in (
        "(assert (= ((_ extract 30 0) left_1) right_2))",
        "(assert (= ((_ extract 31 0) other_left) right_2))",
    ):
        formula = f"(set-logic QF_BV)\n{marker}\n{replacement}\n(check-sat)"
        assert not QueryExecutionRecord(
            query_label="pair-(0,0)",
            premise_digest="b" * 64,
            formula_digest=hashlib.sha256(formula.encode("utf-8")).hexdigest(),
            disposition="unsat",
            proof_kind="pairwise_solver_query",
            formula_text=formula,
            call_site_return_width_receipt_digests=(digest,),
            call_site_return_width_receipt_assertion_digests=(
                (digest, assertion_digest),
            ),
        ).validate()

    replacement = "(assert (= ((_ extract 30 0) left_1) right_2))"
    replacement_digest = hashlib.sha256(replacement.encode("utf-8")).hexdigest()
    forged_marker = (
        f"; call_site_return_width_receipt {digest} "
        f"assertion_sha256={replacement_digest}"
    )
    forged_formula = (
        f"(set-logic QF_BV)\n{forged_marker}\n{replacement}\n(check-sat)"
    )
    assert not QueryExecutionRecord(
        query_label="pair-(0,0)",
        premise_digest="b" * 64,
        formula_digest=hashlib.sha256(forged_formula.encode("utf-8")).hexdigest(),
        disposition="unsat",
        proof_kind="pairwise_solver_query",
        formula_text=forged_formula,
        call_site_return_width_receipt_digests=(digest,),
        call_site_return_width_receipt_assertion_digests=(
            (digest, assertion_digest),
        ),
    ).validate()


def test_parameter_reorder_is_nontrivial_object_correspondence():
    left = [
        {"index": 1, "size": 4, "data_type": "int"},
        {"index": 0, "size": 4, "data_type": "int"},
    ]
    right = [
        {"index": 0, "size": 4, "data_type": "int"},
        {"index": 1, "size": 4, "data_type": "int"},
    ]

    contract = build_input_correspondence_contract(left, right)

    assert not isinstance(contract, BlockedObservation)
    assert [(item[0], item[1]) for item in contract.correspondence_pairs] == [(1, 0), (0, 1)]


def test_runtime_data_type_uses_object_api_identity_without_freezing_wrapper():
    class RuntimeDataType:
        def getDataTypePath(self):
            return "/builtin/int"

        def getName(self):
            return "int"

        def getLength(self):
            return 4

    left = [{
        "index": 0,
        "size": 4,
        "data_type": "int",
        "data_type_obj": RuntimeDataType(),
    }]
    right = [{
        "index": 0,
        "size": 4,
        "data_type": "int",
        "data_type_obj": RuntimeDataType(),
    }]

    contract = build_input_correspondence_contract(left, right)

    assert not isinstance(contract, BlockedObservation)
    assert contract.left_parameter_identities == contract.right_parameter_identities
    assert contract.left_parameter_identities[0][3] == (
        "runtime_data_type", "/builtin/int", "int", 32,
    )


def test_unidentifiable_runtime_data_type_blocks_correspondence():
    class OpaqueRuntimeDataType:
        def __str__(self):
            raise AssertionError("opaque wrapper string must not become identity")

    result = build_input_correspondence_contract(
        [{"index": 0, "size": 4, "data_type_obj": OpaqueRuntimeDataType()}],
        [{"index": 0, "size": 4, "data_type_obj": OpaqueRuntimeDataType()}],
    )

    assert isinstance(result, BlockedObservation)
    assert result.blockers[0].missing_slot == (
        "object_derived_parameter_data_type_identity"
    )


def test_nontrivial_storage_binding_proof_is_bound_to_exact_query_widths():
    left = [{
        "index": 0,
        "size": 4,
        "data_type": "int",
        "storage": {"space_name": "register", "offset": 36, "size": 4},
    }]
    right = [{
        "index": 0,
        "size": 4,
        "data_type": "int",
        "storage": {"space_name": "register", "offset": 32, "size": 4},
    }]
    contract = build_input_correspondence_contract(left, right)
    left_query = (ParameterInfo("value", "value_1", 32, 0),)
    right_query = (ParameterInfo("value", "value_2", 32, 0),)

    proof = prove_object_query_input_correspondence(
        contract, left_query, right_query
    )

    assert proof is not None
    assert proof.applicable_to(contract, left_query, right_query)
    assert not proof.applicable_to(
        contract,
        left_query,
        (ParameterInfo("value", "value_2", 64, 0),),
    )
    assert prove_object_query_input_correspondence(
        contract,
        left_query,
        (ParameterInfo("value", "value_2", 64, 0),),
    ) is None


def test_canonical_query_and_replay_consume_exact_binding_receipt():
    left = _analysis("B-query-left", 0x7300, 32)
    right = _analysis("B-query-right", 0x7400, 64, extension="INT_SEXT")
    parameter_left = ParameterInfo("value", "value_1", 32, 0)
    parameter_right = ParameterInfo("value", "value_2", 32, 0)
    left.parameters = [{"name": "value", "index": 0, "size": 4, "data_type": "int"}]
    right.parameters = [{"name": "value", "index": 0, "size": 4, "data_type": "int"}]
    left_cases = extract_return_cases(left)
    right_cases = extract_return_cases(right)
    prepared_left = prepare_function_return_widths(left, left_cases)
    prepared_right = prepare_function_return_widths(right, right_cases)
    runtime = SimpleNamespace(artifacts=(SimpleNamespace(
        artifact_id=("coverage",),
        is_validated=True,
        premise_digest="coverage-premise",
        payload={"proof": "coverage"},
    ),))
    replace_left = lambda node: node.to_smt(symbol_name_mapping={"value": "value_1"})
    replace_right = lambda node: node.to_smt(symbol_name_mapping={"value": "value_2"})
    prepared = prepare_pair_return_observation(
        left,
        right,
        left_cases[0],
        right_cases[0],
        prepared_left,
        prepared_right,
        return_coverage_ids=(("coverage",),),
        proof_runtime=runtime,
        left_query_parameters=(parameter_left,),
        right_query_parameters=(parameter_right,),
        left_replace_fn=replace_left,
        right_replace_fn=replace_right,
    )
    base_ctx = {
        "params1": [parameter_left],
        "params2": [parameter_right],
        "header_lines": [
            "(declare-fun value_1 () (_ BitVec 32))",
            "(declare-fun value_2 () (_ BitVec 32))",
        ],
        "smt_logic": "QF_BV",
        "return_size1": 32,
        "return_size2": 64,
        "return_width_observations_by_pair": {"(0,0)": prepared},
        "require_original_canonical_return_query_bundle": True,
        "canonical_return_replay_authorization": {
            "bundle_digest": "a" * 64,
            "production_query_digest": "b" * 64,
            "ordered_receipt_digests": (
                prepared.binding_receipt.binding_digest,
            ),
            "binding_projection_order": ("(0,0)",),
        },
    }

    query = build_canonical_return_observation_query(
        base_ctx,
        left_cases[0],
        right_cases[0],
        replace_left,
        replace_right,
        "(0,0)",
        view=prepared.view,
        receipt=prepared.binding_receipt,
    )
    model_assertions = ("(assert (= value_1 (_ bv7 32)))",)
    replay = _build_model_validation_query(
        base_ctx,
        left_cases[0],
        right_cases[0],
        replace_left,
        replace_right,
        model_assertions,
        equality=True,
        pair_id="(0,0)",
    )

    marker = f"; binding-receipt {prepared.binding_receipt.binding_digest}"
    assert marker in query
    assert marker in replay
    model_digest = hashlib.sha256(
        repr(model_assertions).encode("utf-8")
    ).hexdigest()
    assert "canonical_return_replay_authorization" in replay
    assert "production_query_sha256=" + "b" * 64 in replay
    assert "model_assertions_sha256=" + model_digest in replay
    base_ctx["canonical_return_replay_authorization"][
        "ordered_receipt_digests"
    ] = ("f" * 64,)
    with pytest.raises(ValueError, match="replay_authorization_inapplicable"):
        _build_model_validation_query(
            base_ctx,
            left_cases[0],
            right_cases[0],
            replace_left,
            replace_right,
            model_assertions,
            equality=True,
            pair_id="(0,0)",
        )
    base_ctx["canonical_return_replay_authorization"][
        "ordered_receipt_digests"
    ] = (prepared.binding_receipt.binding_digest,)
    base_ctx["params2"] = [ParameterInfo("value", "wrong_symbol", 32, 0)]
    with pytest.raises(ValueError, match="binding_receipt_inapplicable"):
        build_canonical_return_observation_query(
            base_ctx,
            left_cases[0],
            right_cases[0],
            replace_left,
            replace_right,
            "(0,0)",
            view=prepared.view,
            receipt=prepared.binding_receipt,
        )


def test_monolithic_replay_reuses_original_query_bundle_and_fails_closed(monkeypatch):
    from scripts.function_tracer_pcode.proof.strategies import monolithic as module

    left = _analysis("B-monolithic-left", 0x7500, 32)
    right = _analysis("B-monolithic-right", 0x7600, 64, extension="INT_SEXT")
    left_cases = extract_return_cases(left)
    right_cases = extract_return_cases(right)
    prepared = prepare_pair_return_observation(
        left,
        right,
        left_cases[0],
        right_cases[0],
        prepare_function_return_widths(left, left_cases),
        prepare_function_return_widths(right, right_cases),
        return_coverage_ids=(("coverage",),),
        proof_runtime=SimpleNamespace(artifacts=(SimpleNamespace(
            artifact_id=("coverage",),
            is_validated=True,
            premise_digest="coverage-premise",
            payload={"proof": "coverage"},
        ),)),
    )
    assert prepared.proven
    receipt_digest = prepared.binding_receipt.binding_digest
    marker = f"; canonical_return_width_binding_receipt {receipt_digest}"
    production_query = f"(set-logic QF_BV)\n{marker}\n(check-sat)"
    bundle = module._MonolithicReturnWidthQueryBundle(
        canonical_width=32,
        observations_by_pair=(("(0,0)", prepared),),
        left_case_identities=(module._monolithic_case_identity(left_cases[0]),),
        right_case_identities=(module._monolithic_case_identity(right_cases[0]),),
        ordered_receipt_digests=(receipt_digest,),
        ordered_markers=(marker,),
        view_digest="c" * 64,
        binding_digest="d" * 64,
    ).bind_query(production_query)
    context = module._MonolithicDecisionExecutionContext.create(
        left,
        right,
        decision_surface="legacy_source",
        input_correspondence=build_input_correspondence_set(left, right),
    ).with_return_width_query_bundle(bundle)
    strategy = module.MonolithicStrategy(Mock(), Mock())
    base_ctx = {"return_size1": 32, "return_size2": 64}

    monkeypatch.setattr(
        module,
        "prepare_pair_return_observation",
        lambda *_args, **_kwargs: pytest.fail("replay rebuilt a receipt"),
    )
    monkeypatch.setattr(
        _mx_monolithic_return_width,
        "prepare_pair_return_observation",
        lambda *_args, **_kwargs: pytest.fail("replay rebuilt a receipt"),
    )
    assert strategy._bind_original_canonical_return_width_replay_observations(
        context,
        base_ctx,
        left_cases,
        right_cases,
    )
    assert base_ctx["return_width_observations_by_pair"]["(0,0)"] is prepared
    assert base_ctx["canonical_return_replay_authorization"][
        "production_query_digest"
    ] == hashlib.sha256(production_query.encode("utf-8")).hexdigest()

    right_cases[0].index += 1
    assert not strategy._bind_original_canonical_return_width_replay_observations(
        context,
        {"return_size1": 32, "return_size2": 64},
        left_cases,
        right_cases,
    )
    right_cases[0].index -= 1
    invalid_bundle = replace(bundle, production_query_text=production_query + "\n; changed")
    invalid_context = replace(context, return_width_query_bundle=invalid_bundle)
    assert not strategy._bind_original_canonical_return_width_replay_observations(
        invalid_context,
        {"return_size1": 32, "return_size2": 64},
        left_cases,
        right_cases,
    )


def test_pair_coverage_requires_validated_final_artifact_for_both_functions():
    left_identity = ("function_identity_v1", "B8", "left", "0x8000")
    right_identity = ("function_identity_v1", "B9", "right", "0x9000")

    def artifact(identity, ordinal):
        return SimpleNamespace(
            artifact_id=("coverage-artifact", ordinal),
            is_validated=True,
            requirement_id=SimpleNamespace(
                proof_kind="unary_outcome_partition_complete",
                proof_target_key=("function_outcome_seed", identity, "seed", 0),
            ),
        )

    left_only = SimpleNamespace(artifacts=(artifact(left_identity, 1),))
    both = SimpleNamespace(artifacts=(
        artifact(left_identity, 1),
        artifact(right_identity, 2),
    ))

    assert return_coverage_artifact_ids(
        left_only, (left_identity, right_identity)
    ) == ()
    assert return_coverage_artifact_ids(
        both, (left_identity, right_identity)
    ) == (("coverage-artifact", 1), ("coverage-artifact", 2))
