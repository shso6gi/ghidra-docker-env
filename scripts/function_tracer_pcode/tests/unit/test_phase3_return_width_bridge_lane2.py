# -*- coding: utf-8 -*-

import hashlib
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.model import Expression, ReturnInfo
from scripts.function_tracer_pcode.model.runtime_refs import PcodeOpRef
from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.smt.interface import SolverStatus
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import QueryResult, ReturnCase
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_builder import (
    build_return_width_bridge_high_bit_query,
)
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownReasonId,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.equivalence.strategies.base import CheckStrategy
from scripts.function_tracer_pcode.validation.phase3_return_width_bridge_lane2 import (
    build_phase3_return_width_bridge_lane2_manifest,
    build_phase3_return_width_bridge_lane2_post_fix_gate,
    main as phase3_return_width_bridge_lane2_main,
    validate_phase3_return_width_bridge_lane2_manifest,
    validate_phase3_return_width_bridge_lane2_post_fix_gate,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


LEFT_BINARY_NAME = "function_call_test-mips64-clang-O1"
RIGHT_BINARY_NAME = "function_call_test-mips64-gcc-O0"


class _DummyStrategy(CheckStrategy):
    def check(self, analysis1, analysis2, save_formula: bool = False):
        raise NotImplementedError


class _PairwiseReturnWidthHarness(PairwiseStrategy):
    def __init__(self, *results):
        self.enable_completed_recovery_proofs = True
        self._results = [QueryResult(result) for result in results]
        self.solve_calls = []
        self.debug_trace = []

    def _solve_query_internal(
        self,
        query: str,
        pair_id: str,
        stage: str = "full",
        use_hard_timeout: bool = False,
    ) -> QueryResult:
        self.solve_calls.append(
            {
                "query": query,
                "pair_id": pair_id,
                "stage": stage,
                "use_hard_timeout": use_hard_timeout,
            }
        )
        assert self._results, f"unexpected solver query for stage {stage}"
        return self._results.pop(0)

    def _debug_print(self, message: str) -> None:
        self.debug_trace.append(str(message))


class _AnalysisStub:
    def __init__(self):
        self.completed_recovery_proof_evidence = []


def _pcode_ref(binary_id: str, function_entry: int, seq_target: int, *, seq_time: int = 40):
    return [
        "pcode_op",
        binary_id,
        ["function_entry", "ram", function_entry],
        ["seq_target", "ram", seq_target],
        seq_time,
        1,
        10,
        1,
    ]


def _return_case_partition_member(
    *,
    binary_id: str,
    function_entry: int,
    seq_target: int,
    address: str,
    return_width: int,
    case_index: int = 0,
):
    return [
        "return_case_partition_member",
        case_index,
        [case_index],
        [
            "return_case",
            case_index,
            address,
            _pcode_ref(binary_id, function_entry, seq_target),
            f"{address}:t40",
            1,
            ["expression", ["const", ["int", 1], return_width // 8]],
            [
                [
                    "return_guard",
                    True,
                    ["condition", ["const", ["int", 1], 1], True],
                    ["expression", ["const", ["int", 1], 1]],
                ]
            ],
        ],
        ["comparison_surface", "return_value", return_width, None],
        ["value", ["expression", ["const", ["int", 1], return_width // 8]]],
    ]


def _extension_op(
    *,
    binary_id: str = "B13",
    function_entry: int = 4831846228,
    seq_target: int = 4831846336,
    mnemonic: str = "INT_SEXT",
    input_bits: int = 32,
    output_bits: int = 64,
):
    policy = "sign_extend" if mnemonic == "INT_SEXT" else "zero_extend"
    return [
        "extension_op",
        mnemonic,
        ["op_ref", _pcode_ref(binary_id, function_entry, seq_target, seq_time=38)],
        ["input_bits", input_bits],
        ["output_bits", output_bits],
        ["policy", policy],
    ]


def _return_value_width(
    *,
    return_width: int,
    producer_width: int = None,
    signed: bool = False,
    extension_ops=None,
    value=None,
    pcode_input_bits: int = None,
):
    if producer_width is None:
        producer_width = return_width
    if value is None:
        value = ["expression", ["const", ["int", 1], producer_width // 8]]
    if pcode_input_bits is None:
        pcode_input_bits = producer_width
    if producer_width < return_width:
        relation = "producer_narrower_than_return_width"
        policy = "sign_extend" if signed else "zero_extend"
    elif producer_width > return_width:
        relation = "producer_wider_than_return_width"
        policy = "truncate"
    else:
        relation = "producer_matches_return_width"
        policy = "none"
    result = [
        "return_value_width",
        producer_width,
        return_width,
        signed,
        ["value", value],
        relation,
        policy,
        ["expression_bits", producer_width],
        ["return_pcode_value_input_bits", pcode_input_bits],
    ]
    if extension_ops is not None:
        result.append(["return_value_extension_ops", list(extension_ops)])
    return result


def _sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_artifact_manifest(root: Path) -> None:
    root.mkdir(parents=True)
    (root / "artifact_manifest.json").write_text(
        json.dumps(
            {
                "baseline_id": "observed-v0@0a53352",
                "git_head": "0a53352cf3c9528abfb654906ed7b963474bedc5",
            }
        )
    )


def _target(label: str = "case0"):
    return [
        "return_width_bridge",
        ["pair", label],
        ["return_widths", 32, 64],
        [
            "return_width_side",
            "left",
            ["function_ref", ["function", "B10", 1052592]],
            ["return_size", 32],
            ["return_storage", "return_value", 32, None, "int"],
            _return_case_partition_member(
                binary_id="B10",
                function_entry=1052592,
                seq_target=1052644,
                address="00100fe4",
                return_width=32,
            ),
            _return_value_width(return_width=32, signed=True),
        ],
        [
            "return_width_side",
            "right",
            ["function_ref", ["function", "B13", 4831846228]],
            ["return_size", 64],
            ["return_storage", "return_value", 64, None, "long"],
            _return_case_partition_member(
                binary_id="B13",
                function_entry=4831846228,
                seq_target=4831846344,
                address="120001fc8",
                return_width=64,
            ),
            _return_value_width(return_width=64, producer_width=64, signed=True),
        ],
    ]


def _weak_target(label: str = "case0"):
    return [
        "return_width_bridge",
        ["pair", label],
        ["return_widths", 32, 64],
        ["return_width_side", "left", ["function_ref", ["function", "B10", 1052592]]],
        ["return_width_side", "right", ["function_ref", ["function", "B13", 4831846228]]],
    ]


def _weak_target_with_return_case_only(label: str = "case0"):
    return [
        "return_width_bridge",
        ["pair", label],
        ["return_widths", 32, 64],
        [
            "return_width_side",
            "left",
            ["return_case_partition_member", 0, [0], ["return_case", 0, "00100fe4"]],
        ],
        [
            "return_width_side",
            "right",
            ["return_case_partition_member", 0, [0], ["return_case", 0, "120001fc8"]],
        ],
    ]


def _target_with_return_size_mismatch(label: str = "case0"):
    target = json.loads(json.dumps(_target(label)))
    target[3][3] = ["return_size", 64]
    return target


def _target_without_return_value_width(label: str = "case0"):
    target = json.loads(json.dumps(_target(label)))
    target[3] = target[3][:-1]
    target[4] = target[4][:-1]
    return target


def _target_with_right_narrow_extension(label: str = "case0"):
    target = json.loads(json.dumps(_target(label)))
    target[4][-1] = _return_value_width(
        return_width=64,
        producer_width=32,
        signed=True,
        extension_ops=[_extension_op()],
    )
    return target


def _target_with_right_summary_parameter_extension(label: str = "case0"):
    target = json.loads(json.dumps(_target(label)))
    summary_parameter = [
        "expression",
        ["parameter", "summary_rec_10000", ["int", 10000], 4],
    ]
    target[4][5][3][6] = summary_parameter
    target[4][5][5] = ["value", summary_parameter]
    target[4][-1] = _return_value_width(
        return_width=64,
        producer_width=32,
        signed=True,
        value=summary_parameter,
        pcode_input_bits=64,
        extension_ops=[],
    )
    return target


def _target_with_function_ref(label: str, function_ref):
    target = json.loads(json.dumps(_target(label)))
    target[3][2] = ["function_ref", function_ref]
    return target


def _target_with_pair(pair_value):
    target = json.loads(json.dumps(_target("case0")))
    target[1] = ["pair", pair_value]
    return target


def _target_with_extra_missing_diagnostic():
    target = json.loads(json.dumps(_target("case0")))
    target.append(["diagnostic", "<missing>"])
    return target


def _target_with_return_case_member(label: str, return_case_member):
    target = json.loads(json.dumps(_target(label)))
    target[3][5] = return_case_member
    return target


def _valid_left_return_case_member():
    return _return_case_partition_member(
        binary_id="B10",
        function_entry=1052592,
        seq_target=1052644,
        address="00100fe4",
        return_width=32,
    )


def _return_case_member_with_guards(guards):
    member = _valid_left_return_case_member()
    member[3][7] = guards
    return member


def _return_case_member_with_return_value(return_value):
    member = _valid_left_return_case_member()
    member[3][6] = return_value
    return member


def _return_case_member_with_value_evidence(value_evidence):
    member = _valid_left_return_case_member()
    member[5] = value_evidence
    return member


def _return_case_member_with_comparison_surface(comparison_surface):
    member = _valid_left_return_case_member()
    member[4] = comparison_surface
    return member


def _return_case_member_with_guard_condition(condition):
    member = _valid_left_return_case_member()
    member[3][7][0][2] = condition
    return member


def _return_case_member_with_guard_expression(expression):
    member = _valid_left_return_case_member()
    member[3][7][0][3] = expression
    return member


def _width_reason(target=None):
    kwargs = {}
    if target is not None:
        kwargs["object_target_key"] = target
    return make_unknown_reason(UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING, **kwargs)


def _action_payload(action):
    return action if isinstance(action, dict) else action.to_dict()


def _completed_proof_content(action):
    target = action["object_target_key"]
    widths = target[2]
    left = target[3]
    right = target[4]
    left_function_ref = left[2]
    right_function_ref = right[2]
    left_return_storage = left[4]
    right_return_storage = right[4]
    narrow_width = min(widths[1], widths[2])
    wide_width = max(widths[1], widths[2])
    if action["proof_kind"] == "abi_relation_proof":
        return {
            "object_derived": True,
            "status": "proven",
            "object_target_key": target,
            "calling_convention": {
                "object_derived": True,
                "status": "proven",
                "left_function_ref": left_function_ref,
                "right_function_ref": right_function_ref,
                "relation": "same_return_abi_family",
            },
            "return_storage": {
                "object_derived": True,
                "status": "proven",
                "left_return_storage": left_return_storage,
                "right_return_storage": right_return_storage,
                "relation": "abi_related_return_storage",
            },
            "narrow_return_width": {
                "object_derived": True,
                "status": "proven",
                "narrow_width": narrow_width,
                "proven": True,
            },
        }
    if action["proof_kind"] == "high_bit_proof":
        value_width_evidence = ["return_value_width_evidence", left[-1], right[-1]]
        return {
            "object_derived": True,
            "status": "proven",
            "object_target_key": target,
            "producer_width": {
                "object_derived": True,
                "status": "proven",
                "left_width": widths[1],
                "right_width": widths[2],
                "value_width_evidence": value_width_evidence,
            },
            "extension_semantics": {
                "object_derived": True,
                "status": "proven",
                "left_extension": left[-1][6],
                "right_extension": right[-1][6],
                "left_extension_ops": [],
                "right_extension_ops": [],
                "relation": "compatible_under_narrow_width",
            },
            "high_bits_irrelevant_or_equal": {
                "object_derived": True,
                "status": "proven",
                "narrow_width": narrow_width,
                "wide_width": wide_width,
                "proof": "high_bits_do_not_affect_compared_return",
                "proven": True,
                "query_stage": "return-width-bridge-high-bit-extension",
            },
        }
    return {}


def _completed_evidence(actions, *, include_proof_content=True):
    records = []
    for action in actions:
        evidence = {
            "reason_id": action["reason_id"],
            "proof_stage": action["proof_stage"],
            "proof_kind": action["proof_kind"],
            "evidence_kind": action["evidence_kind"],
            "required_evidence": action["required_evidence"],
            "status": "complete",
            "object_derived": True,
            "object_target_key": action["object_target_key"],
            "proof_obligation_id": action["proof_obligation_id"],
            "proof_source": "return_width_bridge_narrow_and_high_bit_queries_unsat",
        }
        if include_proof_content:
            evidence["proof_content"] = _completed_proof_content(action)
        records.append(
            {
                "evidence": {
                    **evidence,
                }
            }
        )
    return records


def _constant_return_case(index: int, value: int, *, size: int, return_type: str):
    expr = Expression.constant(value, size=size)
    return ReturnCase(
        index=index,
        conditions=[],
        value_expr=expr,
        return_info=ReturnInfo(address=f"0x{index:x}", value=expr),
        return_type=return_type,
    )


def _summary_parameter_return_cases():
    expr = Expression.parameter(
        "summary_rec_10000",
        10000,
        data_type="int",
        size=4,
    )
    return (
        ReturnCase(
            index=0,
            conditions=[],
            value_expr=expr,
            return_info=ReturnInfo(address="00100fe4", value=expr),
            return_type="int",
        ),
        ReturnCase(
            index=0,
            conditions=[],
            value_expr=expr,
            return_info=ReturnInfo(address="120001fc8", value=expr),
            return_type="long",
        ),
    )


def _return_width_bridge_pairwise_ctx():
    analysis1 = _AnalysisStub()
    analysis2 = _AnalysisStub()
    return {
        "analysis1": analysis1,
        "analysis2": analysis2,
        "header_lines": [],
        "return_size1": 32,
        "return_size2": 64,
    }, analysis1, analysis2


def _solve_return_width_bridge_with_harness(strategy, target):
    case1, case2 = _summary_parameter_return_cases()
    base_ctx, analysis1, analysis2 = _return_width_bridge_pairwise_ctx()
    result = strategy._solve_return_width_bridge_with_completed_proof(
        base_ctx,
        case1,
        case2,
        None,
        None,
        "(0,0)",
        object_target_key=CheckStrategy._normalize_nested_tuple(target),
        blocking_detail="return width mismatch",
    )
    return result, analysis1, analysis2


def _assert_summary_parameter_high_bit_query_is_unavailable():
    case1, case2 = _summary_parameter_return_cases()
    query = build_return_width_bridge_high_bit_query(
        {"header_lines": []},
        case1,
        case2,
        None,
        None,
        "(0,0)",
        narrow_bits=32,
        return_size1=32,
        return_size2=64,
    )
    assert query is None


def _solve_direct(query: str):
    pytest.importorskip("z3")
    solver = Z3Solver(timeout=5)
    assert solver.check_availability()[0]
    return solver.check_equivalence_direct(query)


def _payload(*, reasons, actions=None, is_equivalent=None, completed_evidence=None):
    raw_reasons = [reason.to_dict() for reason in reasons]
    raw_actions = [
        _action_payload(action)
        for action in (actions if actions is not None else build_unknown_recovery_actions(reasons))
    ]
    return {
        "function1_name": "fc_apply_indirect",
        "function2_name": "fc_apply_indirect",
        "binary1_name": LEFT_BINARY_NAME,
        "binary2_name": RIGHT_BINARY_NAME,
        "is_equivalent": is_equivalent,
        "is_timeout": False,
        "error_message": None,
        "debug_trace": {
            "final_result": is_equivalent,
            "attempts": [
                {
                    "attempt_id": 0,
                    "phase": "P0_BASE",
                    "result": is_equivalent,
                    "transition_reason": "UNKNOWN",
                    "unknown_reasons": raw_reasons,
                }
            ],
        },
        "unknown_reasons": raw_reasons,
        "unknown_recovery_actions": raw_actions,
        "completed_recovery_proof_evidence": list(completed_evidence or ()),
    }


def _write_log(root: Path, payload: dict) -> Path:
    path = root / "fc_apply_indirect" / "fc_apply_indirect_B10_B13.log"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            [
                "Result: UNKNOWN",
                RESULT_JSON_BEGIN,
                json.dumps(payload, indent=2, sort_keys=True),
                RESULT_JSON_END,
                "",
            ]
        )
    )
    return path


def _setup_logs(tmp_path: Path, *, current_payload: dict):
    raw_dir = tmp_path / "raw"
    _write_artifact_manifest(raw_dir)
    baseline_root = raw_dir / "logs" / "function_call"
    current_root = tmp_path / "current"
    _write_log(baseline_root, _payload(reasons=[_width_reason()]))
    _write_log(current_root, current_payload)
    return raw_dir, baseline_root, current_root


def test_return_width_bridge_completed_evidence_is_accepted_by_decision_gate():
    actions = [_action_payload(action) for action in build_unknown_recovery_actions([_width_reason(_target())])]
    evidence = [record["evidence"] for record in _completed_evidence(actions)]

    proof_ids = {
        CheckStrategy._return_width_bridge_proof_id_from_evidence(record)
        for record in evidence
    }

    assert proof_ids == {
        CheckStrategy._normalize_nested_tuple(action["proof_obligation_id"])
        for action in actions
    }


def test_return_width_bridge_high_bit_completed_content_requires_narrow_extension_op():
    target = _target()
    target[4][-1] = _return_value_width(return_width=64, producer_width=32, signed=True)

    assert (
        CheckStrategy._return_width_bridge_completed_proof_content(
            "high_bit_proof",
            target,
            query_stage="return-width-bridge-high-bit-extension",
            narrow_width=32,
        )
        is None
    )


def test_return_width_bridge_high_bit_completed_content_accepts_object_extension_op():
    target = _target_with_right_narrow_extension()
    content = CheckStrategy._return_width_bridge_completed_proof_content(
        "high_bit_proof",
        target,
        query_stage="return-width-bridge-high-bit-extension",
        narrow_width=32,
    )

    assert content is not None
    right_ops = content["extension_semantics"]["right_extension_ops"]
    assert right_ops[0][1] == "INT_SEXT"
    assert CheckStrategy._return_width_bridge_high_bit_proof_content_is_complete(
        content,
        CheckStrategy._normalize_nested_tuple(target),
    )


def test_return_width_bridge_high_bit_completed_content_rejects_summary_parameter_as_query_proof():
    target = _target_with_right_summary_parameter_extension()
    content = CheckStrategy._return_width_bridge_completed_proof_content(
        "high_bit_proof",
        target,
        query_stage="return-width-bridge-high-bit-extension",
        narrow_width=32,
    )

    assert content is None


def test_return_width_bridge_high_bit_completed_content_accepts_summary_parameter_extension():
    target = _target_with_right_summary_parameter_extension()
    content = CheckStrategy._return_width_bridge_completed_proof_content(
        "high_bit_proof",
        target,
        query_stage="summary-parameter-extension-object-evidence",
        narrow_width=32,
    )

    assert content is not None
    extension_semantics = content["extension_semantics"]
    assert extension_semantics["right_extension_ops"] == ()
    assert extension_semantics["right_summary_parameter_extension"] == (
        (
            "summary_parameter_extension",
            (
                "parameter",
                (
                    "parameter",
                    "summary_rec_10000",
                    ("index", 10000),
                    ("size_bits", 32),
                ),
            ),
            ("producer_bits", 32),
            ("return_bits", 64),
            ("return_pcode_value_input_bits", 64),
            ("policy", "sign_extend"),
            ("parameter_kind", "synthetic_recursive_summary"),
        ),
    )
    assert CheckStrategy._return_width_bridge_high_bit_proof_content_is_complete(
        content,
        CheckStrategy._normalize_nested_tuple(target),
    )


def test_return_width_bridge_completed_evidence_accepts_summary_parameter_extension_source():
    actions = [
        _action_payload(action)
        for action in build_unknown_recovery_actions(
            [_width_reason(_target_with_right_summary_parameter_extension())]
        )
    ]
    evidence = [record["evidence"] for record in _completed_evidence(actions)]
    for record in evidence:
        record["proof_source"] = (
            "return_width_bridge_narrow_query_unsat_and_summary_parameter_extension"
        )
        record["proof_content"] = CheckStrategy._return_width_bridge_completed_proof_content(
            record["proof_kind"],
            CheckStrategy._normalize_nested_tuple(record["object_target_key"]),
            query_stage="summary-parameter-extension-object-evidence",
            narrow_width=32,
        )

    proof_ids = {
        CheckStrategy._return_width_bridge_proof_id_from_evidence(record)
        for record in evidence
    }

    assert proof_ids == {
        CheckStrategy._normalize_nested_tuple(action["proof_obligation_id"])
        for action in actions
    }


def test_return_width_bridge_completed_evidence_rejects_summary_target_as_high_bit_query_proof():
    actions = [
        _action_payload(action)
        for action in build_unknown_recovery_actions(
            [_width_reason(_target_with_right_summary_parameter_extension())]
        )
    ]
    evidence = [record["evidence"] for record in _completed_evidence(actions)]
    for record in evidence:
        if record["proof_kind"] != "high_bit_proof":
            continue
        record["proof_source"] = "return_width_bridge_narrow_and_high_bit_queries_unsat"
        record["proof_content"] = CheckStrategy._return_width_bridge_completed_proof_content(
            record["proof_kind"],
            CheckStrategy._normalize_nested_tuple(record["object_target_key"]),
            query_stage="summary-parameter-extension-object-evidence",
            narrow_width=32,
        )
        record["proof_content"]["high_bits_irrelevant_or_equal"]["proof"] = (
            "high_bits_do_not_affect_compared_return"
        )
        record["proof_content"]["high_bits_irrelevant_or_equal"]["query_stage"] = (
            "return-width-bridge-high-bit-extension"
        )

    accepted = [
        record
        for record in evidence
        if CheckStrategy._return_width_bridge_proof_id_from_evidence(record) is not None
    ]

    assert {record["proof_kind"] for record in accepted} == {"abi_relation_proof"}


def test_return_width_bridge_completed_evidence_rejects_summary_content_with_high_bit_query_source():
    actions = [
        _action_payload(action)
        for action in build_unknown_recovery_actions(
            [_width_reason(_target_with_right_summary_parameter_extension())]
        )
    ]
    evidence = [record["evidence"] for record in _completed_evidence(actions)]
    for record in evidence:
        if record["proof_kind"] != "high_bit_proof":
            continue
        record["proof_source"] = "return_width_bridge_narrow_and_high_bit_queries_unsat"
        record["proof_content"] = CheckStrategy._return_width_bridge_completed_proof_content(
            record["proof_kind"],
            CheckStrategy._normalize_nested_tuple(record["object_target_key"]),
            query_stage="summary-parameter-extension-object-evidence",
            narrow_width=32,
        )

    accepted = [
        record
        for record in evidence
        if CheckStrategy._return_width_bridge_proof_id_from_evidence(record) is not None
    ]

    assert {record["proof_kind"] for record in accepted} == {"abi_relation_proof"}


def test_return_width_bridge_completed_evidence_rejects_summary_source_without_summary_content():
    actions = [_action_payload(action) for action in build_unknown_recovery_actions([_width_reason(_target())])]
    evidence = [record["evidence"] for record in _completed_evidence(actions)]
    for record in evidence:
        record["proof_source"] = (
            "return_width_bridge_narrow_query_unsat_and_summary_parameter_extension"
        )
        if record["proof_kind"] == "high_bit_proof":
            record["proof_content"]["high_bits_irrelevant_or_equal"]["proof"] = (
                "summary_parameter_high_bits_follow_return_abi_extension"
            )
            record["proof_content"]["high_bits_irrelevant_or_equal"]["query_stage"] = (
                "summary-parameter-extension-object-evidence"
            )

    accepted = [
        record
        for record in evidence
        if CheckStrategy._return_width_bridge_proof_id_from_evidence(record) is not None
    ]

    assert {record["proof_kind"] for record in accepted} == {"abi_relation_proof"}


def test_return_width_bridge_high_bit_completed_content_rejects_summary_parameter_without_wide_input():
    target = _target_with_right_summary_parameter_extension()
    target[4][-1][-2] = ["return_pcode_value_input_bits", 32]

    assert (
        CheckStrategy._return_width_bridge_completed_proof_content(
            "high_bit_proof",
            target,
            query_stage="return-width-bridge-high-bit-extension",
            narrow_width=32,
        )
        is None
    )


def test_return_width_bridge_object_key_records_return_value_extension_ops():
    expr = Expression.constant(1, size=4)
    ref = PcodeOpRef(
        binary_id="B13",
        function_entry_space="ram",
        function_entry_offset=4831846228,
        target_space="ram",
        target_offset=4831846336,
        seq_time=38,
        seq_order=1,
        opcode=17,
        local_op_ordinal=1,
        mnemonic="INT_SEXT",
        input_sizes=(4,),
        output_size=8,
    )
    return_info = ReturnInfo(
        address="120001fc8",
        value=expr,
        return_value_pcode_op_refs=(ref,),
    )
    case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=expr,
        return_info=return_info,
        return_type="long",
    )

    width_key = _DummyStrategy(None, None)._return_width_bridge_return_value_width_object_key(
        case,
        return_info,
        64,
    )

    extension_ops = width_key[-1]
    assert extension_ops[0] == "return_value_extension_ops"
    assert extension_ops[1][0][1] == "INT_SEXT"
    assert ("input_bits", 32) in extension_ops[1][0]
    assert ("output_bits", 64) in extension_ops[1][0]


def test_return_value_pcode_op_refs_do_not_recurse_through_phi_inputs():
    class FakeVarnode:
        def __init__(self, size, defining_op=None):
            self._size = size
            self._defining_op = defining_op

        def getDef(self):
            return self._defining_op

        def getSize(self):
            return self._size

    class FakePcodeOp:
        def __init__(self, mnemonic, opcode, inputs, output):
            self._mnemonic = mnemonic
            self._opcode = opcode
            self._inputs = tuple(inputs)
            self._output = output

        def getMnemonic(self):
            return self._mnemonic

        def getOpcode(self):
            return self._opcode

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return self._output

        def getSeqnum(self):
            return None

        def getParent(self):
            return None

    narrow = FakeVarnode(4)
    widened = FakeVarnode(8)
    ext_op = FakePcodeOp("INT_SEXT", 17, [narrow], widened)
    widened._defining_op = ext_op
    other = FakeVarnode(8)
    phi_output = FakeVarnode(8)
    phi_op = FakePcodeOp("MULTIEQUAL", 56, [widened, other], phi_output)
    phi_output._defining_op = phi_op

    refs = ReturnAnalyzer(None, binary_id="B-test")._return_value_pcode_op_refs_from_varnode(
        phi_output
    )

    assert [ref.mnemonic for ref in refs] == ["MULTIEQUAL"]
    assert all(ref.mnemonic != "INT_SEXT" for ref in refs)


def test_return_width_bridge_completed_evidence_rejects_metadata_only_proof():
    actions = [_action_payload(action) for action in build_unknown_recovery_actions([_width_reason(_target())])]
    evidence = [record["evidence"] for record in _completed_evidence(actions, include_proof_content=False)]

    assert all(
        CheckStrategy._return_width_bridge_proof_id_from_evidence(record) is None
        for record in evidence
    )


def test_return_width_bridge_completed_evidence_rejects_missing_proof_source():
    actions = [_action_payload(action) for action in build_unknown_recovery_actions([_width_reason(_target())])]
    evidence = [record["evidence"] for record in _completed_evidence(actions)]
    for record in evidence:
        record.pop("proof_source")

    assert all(
        CheckStrategy._return_width_bridge_proof_id_from_evidence(record) is None
        for record in evidence
    )


def test_return_width_bridge_completed_evidence_rejects_narrow_only_proof_source():
    actions = [_action_payload(action) for action in build_unknown_recovery_actions([_width_reason(_target())])]
    evidence = [record["evidence"] for record in _completed_evidence(actions)]
    for record in evidence:
        record["proof_source"] = "return_width_bridge_narrow_query_unsat"

    assert all(
        CheckStrategy._return_width_bridge_proof_id_from_evidence(record) is None
        for record in evidence
    )


def test_return_width_bridge_completed_evidence_rejects_bogus_high_bit_content():
    actions = [_action_payload(action) for action in build_unknown_recovery_actions([_width_reason(_target())])]
    evidence = [record["evidence"] for record in _completed_evidence(actions)]
    for record in evidence:
        if record["proof_kind"] == "high_bit_proof":
            record["proof_content"]["high_bits_irrelevant_or_equal"]["proof"] = "metadata_only"

    accepted = [
        record
        for record in evidence
        if CheckStrategy._return_width_bridge_proof_id_from_evidence(record) is not None
    ]

    assert {record["proof_kind"] for record in accepted} == {"abi_relation_proof"}


def test_return_width_bridge_completed_evidence_rejects_missing_high_bit_query_stage():
    actions = [_action_payload(action) for action in build_unknown_recovery_actions([_width_reason(_target())])]
    evidence = [record["evidence"] for record in _completed_evidence(actions)]
    for record in evidence:
        if record["proof_kind"] == "high_bit_proof":
            record["proof_content"]["high_bits_irrelevant_or_equal"].pop("query_stage")

    accepted = [
        record
        for record in evidence
        if CheckStrategy._return_width_bridge_proof_id_from_evidence(record) is not None
    ]

    assert {record["proof_kind"] for record in accepted} == {"abi_relation_proof"}


def test_return_width_bridge_completed_evidence_rejects_missing_value_width_evidence():
    actions = [_action_payload(action) for action in build_unknown_recovery_actions([_width_reason(_target())])]
    evidence = [record["evidence"] for record in _completed_evidence(actions)]
    for record in evidence:
        if record["proof_kind"] == "high_bit_proof":
            record["proof_content"]["producer_width"].pop("value_width_evidence")

    accepted = [
        record
        for record in evidence
        if CheckStrategy._return_width_bridge_proof_id_from_evidence(record) is not None
    ]

    assert {record["proof_kind"] for record in accepted} == {"abi_relation_proof"}


def test_return_width_bridge_high_bit_query_rejects_low_bits_only_near_miss():
    narrow_case = _constant_return_case(0, 0, size=4, return_type="unsigned int")
    wide_case = _constant_return_case(0, 0x0000000100000000, size=8, return_type="unsigned long")

    query = build_return_width_bridge_high_bit_query(
        {"header_lines": []},
        narrow_case,
        wide_case,
        None,
        None,
        "(0,0)",
        narrow_bits=32,
        return_size1=32,
        return_size2=64,
    )

    assert query is not None
    result = _solve_direct(query)
    assert result.status == SolverStatus.SAT


def test_return_width_bridge_high_bit_query_proves_signed_extension():
    narrow_case = _constant_return_case(0, 0xFFFFFED4, size=4, return_type="int")
    wide_case = _constant_return_case(0, 0xFFFFFFFFFFFFFED4, size=8, return_type="long")

    query = build_return_width_bridge_high_bit_query(
        {"header_lines": []},
        narrow_case,
        wide_case,
        None,
        None,
        "(0,0)",
        narrow_bits=32,
        return_size1=32,
        return_size2=64,
    )

    assert query is not None
    result = _solve_direct(query)
    assert result.status == SolverStatus.UNSAT


def test_return_width_bridge_high_bit_query_rejects_missing_wide_bits():
    narrow_case = _constant_return_case(0, 0, size=4, return_type="unsigned int")
    wide_case = _constant_return_case(0, 0, size=4, return_type="unsigned long")

    query = build_return_width_bridge_high_bit_query(
        {"header_lines": []},
        narrow_case,
        wide_case,
        None,
        None,
        "(0,0)",
        narrow_bits=32,
        return_size1=32,
        return_size2=64,
    )

    assert query is None


def test_pairwise_return_width_bridge_summary_parameter_fallback_completes_after_narrow_unsat():
    target = _target_with_right_summary_parameter_extension("(0,0)")
    strategy = _PairwiseReturnWidthHarness(True)

    _assert_summary_parameter_high_bit_query_is_unavailable()
    result, analysis1, analysis2 = _solve_return_width_bridge_with_harness(strategy, target)

    assert result is not None
    assert result.is_equivalent is True
    assert result.pair_stage == "return-width-bridge-narrow-ineq"
    assert [call["stage"] for call in strategy.solve_calls] == [
        "return-width-bridge-narrow-ineq"
    ]
    assert strategy._results == []
    completed = list(analysis1.completed_recovery_proof_evidence)
    assert analysis2.completed_recovery_proof_evidence == []
    assert {record["proof_kind"] for record in completed} == {
        "abi_relation_proof",
        "high_bit_proof",
    }
    high_bit = next(record for record in completed if record["proof_kind"] == "high_bit_proof")
    assert high_bit["proof_source"] == (
        "return_width_bridge_narrow_query_unsat_and_summary_parameter_extension"
    )
    assert high_bit["proof_content"]["high_bits_irrelevant_or_equal"] == {
        "object_derived": True,
        "status": "proven",
        "narrow_width": 32,
        "wide_width": 64,
        "proof": "summary_parameter_high_bits_follow_return_abi_extension",
        "proven": True,
        "query_stage": "summary-parameter-extension-object-evidence",
    }
    assert high_bit["proof_content"]["extension_semantics"][
        "right_summary_parameter_extension"
    ]


def test_pairwise_return_width_bridge_summary_parameter_fallback_rejects_without_summary_extension():
    target = _target("(0,0)")
    strategy = _PairwiseReturnWidthHarness(True)

    result, analysis1, analysis2 = _solve_return_width_bridge_with_harness(strategy, target)

    assert result is None
    assert [call["stage"] for call in strategy.solve_calls] == [
        "return-width-bridge-narrow-ineq"
    ]
    assert analysis1.completed_recovery_proof_evidence == []
    assert analysis2.completed_recovery_proof_evidence == []


def test_pairwise_return_width_bridge_summary_parameter_fallback_rejects_when_narrow_query_not_unsat():
    target = _target_with_right_summary_parameter_extension("(0,0)")
    strategy = _PairwiseReturnWidthHarness(False)

    result, analysis1, analysis2 = _solve_return_width_bridge_with_harness(strategy, target)

    assert result is None
    assert [call["stage"] for call in strategy.solve_calls] == [
        "return-width-bridge-narrow-ineq"
    ]
    assert analysis1.completed_recovery_proof_evidence == []
    assert analysis2.completed_recovery_proof_evidence == []


def test_phase3_return_width_bridge_lane2_manifest_and_post_fix_gate_ready(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is True
    validate_phase3_return_width_bridge_lane2_manifest(manifest)
    tampered_manifest = json.loads(json.dumps(manifest))
    tampered_manifest["readiness"]["failure_kinds"] = ["hidden_lane2_failure"]
    with pytest.raises(ValueError, match="hidden_lane2_failure"):
        validate_phase3_return_width_bridge_lane2_manifest(tampered_manifest)

    entry = manifest["entries"][0]
    assert len(entry["target_object_keys"]) == 1
    assert {action["proof_stage"] for action in entry["required_completion_actions"]} == {
        "abi_relation",
        "high_bit_relation",
    }
    assert all(action["proof_obligation_id"] for action in entry["required_completion_actions"])

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "pending_proof"
    obligations = gate["entries"][0]["pending_proof_obligations"]
    assert {obligation["proof_stage"] for obligation in obligations} == {
        "abi_relation",
        "high_bit_relation",
    }
    assert all(
        obligation["reason_id"] == "return_width_bridge_missing"
        and obligation["completed_evidence_present"] is False
        and obligation["status"] == "pending_evidence"
        and obligation["proof_obligation_id"]
        for obligation in obligations
    )
    validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)
    tampered_gate = json.loads(json.dumps(gate))
    tampered_gate["post_fix_regression_gate"]["summary"]["failed_kinds"] = ["hidden_lane2_post_fix_failure"]
    with pytest.raises(ValueError, match="hidden_lane2_post_fix_failure"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(tampered_gate)
    tampered_pre_fix = json.loads(pre_fix_path.read_text())
    tampered_pre_fix["readiness"]["failure_kinds"] = ["hidden_lane2_pre_fix_manifest_failure"]
    tampered_pre_fix_path = pre_fix_path.with_name(
        "tampered_return_width_bridge_lane2_representatives.json"
    )
    tampered_pre_fix_path.write_text(json.dumps(tampered_pre_fix))
    tampered_pre_fix_gate_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate-tampered-pre-fix",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=tampered_pre_fix_path,
        phase3_manifest_sha256=_sha256_path(tampered_pre_fix_path),
    )
    tampered_pre_fix_gate = json.loads(tampered_pre_fix_gate_path.read_text())
    assert tampered_pre_fix_gate["phase3_lane2_post_fix_ready"] is False
    assert (
        "phase3_pre_fix_manifest_ready"
        in tampered_pre_fix_gate["post_fix_regression_gate"]["summary"]["failed_kinds"]
    )
    ready_check = next(
        check
        for check in tampered_pre_fix_gate["post_fix_regression_gate"]["checks"]
        if check["kind"] == "phase3_pre_fix_manifest_ready"
    )
    assert ready_check["status"] == "failed"
    assert "hidden_lane2_pre_fix_manifest_failure" in ready_check["error"]
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_ready"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(tampered_pre_fix_gate)


def test_phase3_return_width_bridge_lane2_post_fix_accepts_partial_target_progress(tmp_path):
    original_target = _target_without_return_value_width("case0")
    remaining_target = _target_without_return_value_width("case1")
    current_payload = _payload(
        reasons=[
            _width_reason(original_target),
            _width_reason(remaining_target),
        ]
    )
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    original_completed_actions = [
        _action_payload(action)
        for action in build_unknown_recovery_actions([_width_reason(_target("case0"))])
    ]
    _write_log(
        current_root,
        _payload(
            reasons=[_width_reason(_target("case1"))],
            completed_evidence=_completed_evidence(original_completed_actions),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())

    assert gate["phase3_lane2_post_fix_ready"] is True
    entry = gate["entries"][0]
    assert entry["post_fix_status"] == "pending_proof"
    assert entry["post_fix_failures"] == []
    obligations = entry["pending_proof_obligations"]
    required_actions = entry["required_completion_actions"]
    assert len(required_actions) == 2
    assert {action["proof_stage"] for action in required_actions} == {
        "abi_relation",
        "high_bit_relation",
    }
    assert all(action["proof_obligation_id"][-1][1] == ["pair", "case1"] for action in required_actions)
    assert {obligation["proof_stage"] for obligation in obligations} == {
        "abi_relation",
        "high_bit_relation",
    }
    assert all(
        obligation["completed_evidence_present"] is False
        and obligation["proof_obligation_id"][-1][1] == ["pair", "case1"]
        for obligation in obligations
    )
    validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_rejects_target_change_without_completed_proof(
    tmp_path,
):
    current_payload = _payload(reasons=[_width_reason(_target_without_return_value_width("case0"))])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    _write_log(current_root, _payload(reasons=[_width_reason(_target("case1"))]))

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())

    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert any(
        failure["kind"] == "return_width_bridge_target_set_changed"
        for failure in gate["entries"][0]["post_fix_failures"]
    )
    with pytest.raises(ValueError, match="return_width_bridge_post_fix_expected_movement"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_rejects_added_current_target(tmp_path):
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[_width_reason(_target("case0"))]),
    )
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    _write_log(
        current_root,
        _payload(
            reasons=[
                _width_reason(_target("case0")),
                _width_reason(_target("case1")),
            ],
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())

    assert gate["phase3_lane2_post_fix_ready"] is False
    failures = gate["entries"][0]["post_fix_failures"]
    assert any(
        failure["kind"] == "return_width_bridge_target_set_changed"
        and failure["unexpected_current_targets"]
        for failure in failures
    )
    with pytest.raises(ValueError, match="return_width_bridge_post_fix_expected_movement"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_rejects_current_action_set_drift(tmp_path):
    reason = _width_reason(_target("case0"))
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    actions = [_action_payload(action) for action in build_unknown_recovery_actions([reason])]
    high_bit_action = next(action for action in actions if action["proof_stage"] == "high_bit_relation")
    actions[0] = json.loads(json.dumps(high_bit_action))
    _write_log(current_root, _payload(reasons=[reason], actions=actions))

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())

    assert gate["phase3_lane2_post_fix_ready"] is False
    failures = gate["entries"][0]["post_fix_failures"]
    assert any(
        failure["kind"] == "return_width_bridge_required_actions_changed"
        and failure["expected_action_keys"] != failure["actual_action_keys"]
        for failure in failures
    )
    with pytest.raises(ValueError, match="return_width_bridge_post_fix_expected_movement"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_manifest_rejects_missing_high_bit_action(tmp_path):
    reason = _width_reason(_target())
    actions = [
        action
        for action in build_unknown_recovery_actions([reason])
        if action.proof_stage != "high_bit_relation"
    ]
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_actions_complete" in manifest["readiness"]["failure_kinds"]
    with pytest.raises(ValueError, match="return_width_bridge_current_actions_complete"):
        validate_phase3_return_width_bridge_lane2_manifest(manifest)


def test_phase3_return_width_bridge_lane2_manifest_rejects_malformed_proof_id(tmp_path):
    reason = _width_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    actions[0]["proof_obligation_id"] = ["not", "the", "full", "key"]
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_actions_complete" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_rejects_wrong_action_metadata(tmp_path):
    reason = _width_reason(_target())
    actions = [action.to_dict() for action in build_unknown_recovery_actions([reason])]
    actions[0]["evidence_kind"] = "not_expected_evidence"
    actions[0]["required_evidence"] = ["wrong"]
    actions[0]["status"] = "unexpected_status"
    actions[0]["proof_obligation_id"] = build_proof_obligation_id(
        actions[0]["reason_id"],
        actions[0]["proof_stage"],
        actions[0]["proof_kind"],
        actions[0]["evidence_kind"],
        actions[0]["object_target_key"],
    )
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason], actions=actions),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_actions_complete" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_rejects_weak_object_target(tmp_path):
    reason = _width_reason(_weak_target())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_rejects_return_case_only_target(tmp_path):
    reason = _width_reason(_weak_target_with_return_case_only())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_rejects_side_return_size_mismatch(tmp_path):
    reason = _width_reason(_target_with_return_size_mismatch())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_accepts_legacy_target_without_return_value_width(tmp_path):
    reason = _width_reason(_target_without_return_value_width())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is True
    assert "return_width_bridge_current_targets_present" not in manifest["readiness"]["failure_kinds"]


@pytest.mark.parametrize(
    "function_ref",
    [
        ["function", None, 1052592],
        ["function", "", 1052592],
        ["function", "<missing>", 1052592],
        ["function", "B10", None],
        ["function", "B10", True],
        ["function", "123", 1052592],
        ["entry_point", "B10", 1052592],
    ],
)
def test_phase3_return_width_bridge_lane2_manifest_rejects_weak_function_ref(
    tmp_path,
    function_ref,
):
    reason = _width_reason(_target_with_function_ref("case0", function_ref))
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


@pytest.mark.parametrize("pair_value", [[], 0, "", "<missing>"])
def test_phase3_return_width_bridge_lane2_manifest_rejects_weak_pair_tag(tmp_path, pair_value):
    reason = _width_reason(_target_with_pair(pair_value))
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_manifest_rejects_missing_sentinel_in_target(
    tmp_path,
):
    reason = _width_reason(_target_with_extra_missing_diagnostic())
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


@pytest.mark.parametrize(
    "return_case_member",
    [
        ["return_case_partition_member"],
        ["return_case_partition_member", None, [], None],
        [
            "return_case_partition_member",
            0,
            [],
            [
                "return_case",
                0,
                "00100fe4",
                _pcode_ref("B10", 1052592, 1052644),
                "00100fe4:t40",
                1,
                ["expression", ["const", ["int", 1], 4]],
                [],
            ],
            ["comparison_surface", "return_value", 32, None],
            ["value", ["expression", ["const", ["int", 1], 4]]],
        ],
        [
            "return_case_partition_member",
            0,
            [0],
            ["return_case", None, None],
            ["comparison_surface", "return_value", 32, None],
            ["value", ["expression", ["const", ["int", 1], 4]]],
        ],
        [
            "return_case_partition_member",
            0,
            [0],
            [
                "return_case",
                0,
                "00100fe4",
                ["pcode_op", "B10"],
                "00100fe4:t40",
                1,
                ["expression", ["const", ["int", 1], 4]],
                [],
            ],
            ["comparison_surface", "return_value", 32, None],
            ["value", ["expression", ["const", ["int", 1], 4]]],
        ],
        [
            "return_case_partition_member",
            0,
            [0],
            [
                "return_case",
                0,
                "00100fe4",
                _pcode_ref("B10", 1052592, 1052644),
                "00100fe4:t40",
                1,
                ["expression", ["const", ["int", 1], 4]],
                [],
            ],
            ["comparison_surface", "return_value", 64, None],
            ["value", ["expression", ["const", ["int", 1], 4]]],
        ],
        [
            "return_case_partition_member",
            0,
            [0],
            [
                "return_case",
                0,
                "00100fe4",
                _pcode_ref("B10", 1052592, 1052644),
                "00100fe4:t40",
                1,
                ["expression", ["const", ["int", 1], 4]],
                [],
            ],
            ["comparison_surface", "return_value", 32, None],
            ["value", None],
        ],
        _return_case_member_with_guards([]),
        _return_case_member_with_return_value("raw-prose-ish-return-value"),
        _return_case_member_with_return_value(["expression", "raw-prose-ish-return-value"]),
        _return_case_member_with_return_value(
            ["expression", ["const", "raw-prose-ish-return-value", 4]]
        ),
        _return_case_member_with_return_value(
            ["expression", ["const", ["bytes", "raw-prose-ish"], 4]]
        ),
        _return_case_member_with_return_value(
            [
                "expression",
                [
                    "memory",
                    32,
                    ["const", ["int", 1], 8],
                    ["read_order", "raw-prose-ish-order"],
                ],
            ]
        ),
        _return_case_member_with_return_value(
            [
                "expression",
                [
                    "memory",
                    32,
                    ["const", ["int", 1], 8],
                    ["read_order", None],
                ],
            ]
        ),
        _return_case_member_with_return_value(
            ["expression", ["call", "raw-prose-ish-callee", 4, []]]
        ),
        _return_case_member_with_return_value(
            [
                "expression",
                [
                    "call",
                    ["unknown_indirect_target", "raw-prose-ish-callee"],
                    4,
                    [],
                ],
            ]
        ),
        _return_case_member_with_return_value(
            [
                "expression",
                [
                    "call",
                    [
                        "unknown_indirect_target",
                        ["typed_target_expression", ["expression", ["parameter", "fp", ["int", 0], 8]]],
                        ["provenance", "raw-prose-ish-provenance"],
                    ],
                    4,
                    [],
                ],
            ]
        ),
        _return_case_member_with_return_value(
            ["expression", ["call", ["call_target", "raw-prose-ish-callee"], 4, []]]
        ),
        _return_case_member_with_return_value(
            [
                "expression",
                [
                    "call",
                    ["external_symbol", "raw-prose-ish-lib", "raw-prose-ish-name"],
                    4,
                    [],
                ],
            ]
        ),
        _return_case_member_with_return_value(
            ["expression", ["call", ["import_stub", "raw-prose-ish-import"], 4, []]]
        ),
        _return_case_member_with_return_value(
            ["expression", ["call", ["thunk", "raw-prose-ish-thunk"], 4, []]]
        ),
        _return_case_member_with_return_value(
            ["expression", ["raw-prose-ish-node", "raw-prose-ish-return-value"]]
        ),
        _return_case_member_with_value_evidence(["value", "raw-prose-ish-value-evidence"]),
        _return_case_member_with_value_evidence(
            ["value", ["expression", "raw-prose-ish-value-evidence"]]
        ),
        _return_case_member_with_value_evidence(
            ["value", ["expression", ["const", "raw-prose-ish-value-evidence", 4]]]
        ),
        _return_case_member_with_value_evidence(
            ["value", ["expression", ["raw-prose-ish-node", "raw-prose-ish-value-evidence"]]]
        ),
        _return_case_member_with_comparison_surface(["comparison_surface", "memory_effect", 32, None]),
        _return_case_member_with_guard_condition("raw-prose-ish-guard-condition"),
        _return_case_member_with_guard_condition(["condition", "raw-prose-ish-guard-condition"]),
        _return_case_member_with_guard_condition(
            ["condition", ["const", "raw-prose-ish-guard-condition", 1], True]
        ),
        _return_case_member_with_guard_condition(
            ["condition", ["raw-prose-ish-node", "raw-prose-ish-guard-condition"], True]
        ),
        _return_case_member_with_guard_expression("raw-prose-ish-guard-expression"),
        _return_case_member_with_guard_expression(["expression", "raw-prose-ish-guard-expression"]),
        _return_case_member_with_guard_expression(
            ["expression", ["const", "raw-prose-ish-guard-expression", 1]]
        ),
        _return_case_member_with_guard_expression(
            ["expression", ["raw-prose-ish-node", "raw-prose-ish-guard-expression"]]
        ),
    ],
)
def test_phase3_return_width_bridge_lane2_manifest_rejects_weak_return_case_member(
    tmp_path,
    return_case_member,
):
    reason = _width_reason(_target_with_return_case_member("case0", return_case_member))
    raw_dir, baseline_root, current_root = _setup_logs(
        tmp_path,
        current_payload=_payload(reasons=[reason]),
    )

    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    manifest = json.loads(pre_fix_path.read_text())
    assert manifest["phase3_lane2_ready"] is False
    assert "return_width_bridge_current_targets_present" in manifest["readiness"]["failure_kinds"]


def test_phase3_return_width_bridge_lane2_post_fix_requires_manifest_sha256(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    failed = gate["post_fix_regression_gate"]["summary"]["failed_kinds"]
    assert "phase3_pre_fix_manifest_sha256_required" in failed
    with pytest.raises(ValueError, match="phase3_pre_fix_manifest_sha256_required"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_without_completed_proof(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    _write_log(current_root, _payload(reasons=[], actions=[], is_equivalent=True))

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert gate["entries"][0]["post_fix_failures"][0]["kind"] == "return_width_bridge_completed_proof_required"
    with pytest.raises(ValueError, match="return_width_bridge_post_fix_expected_movement"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_accepts_eq_with_completed_proof(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=_completed_evidence(required_actions),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is True
    assert gate["entries"][0]["post_fix_status"] == "completed_recovery"
    validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_changed_return_value_width(
    tmp_path,
):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    completed_evidence = _completed_evidence(required_actions)

    for record in completed_evidence:
        evidence = record["evidence"]
        if evidence.get("reason_id") != UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value:
            continue
        changed_target = json.loads(json.dumps(evidence["object_target_key"]))
        changed_target[4][-1] = _return_value_width(
            return_width=64,
            producer_width=32,
            signed=False,
        )
        proof_kind = evidence["proof_kind"]
        evidence["object_target_key"] = changed_target
        evidence["proof_obligation_id"] = build_proof_obligation_id(
            evidence["reason_id"],
            evidence["proof_stage"],
            proof_kind,
            evidence["evidence_kind"],
            changed_target,
        )
        evidence["proof_content"] = CheckStrategy._return_width_bridge_completed_proof_content(
            proof_kind,
            CheckStrategy._normalize_nested_tuple(changed_target),
            query_stage="return-width-bridge-high-bit-extension",
            narrow_width=32,
        )

    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=completed_evidence,
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert {
        failure["kind"] for failure in gate["entries"][0]["post_fix_failures"]
    } == {"return_width_bridge_completed_proof_required"}


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_metadata_only_completed_proof(
    tmp_path,
):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=_completed_evidence(
                required_actions,
                include_proof_content=False,
            ),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert {
        failure["kind"] for failure in gate["entries"][0]["post_fix_failures"]
    } == {"return_width_bridge_completed_proof_required"}


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_missing_required_evidence(
    tmp_path,
):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    completed_evidence = _completed_evidence(required_actions)
    completed_evidence[0]["evidence"].pop("required_evidence")
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=completed_evidence,
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert any(
        failure["kind"] == "return_width_bridge_completed_proof_required"
        and failure["proof_stage"] == "abi_relation"
        for failure in gate["entries"][0]["post_fix_failures"]
    )


@pytest.mark.parametrize(
    "mutation",
    [
        "missing_proof_source",
        "narrow_only_proof_source",
        "summary_proof_source_for_high_bit_query_content",
        "bogus_calling_convention_relation",
        "missing_calling_convention_status",
        "bogus_extension_relation",
        "missing_extension_status",
        "wrong_extension_policy",
        "missing_value_width_evidence",
        "bogus_high_bit_proof_label",
        "missing_high_bit_query_stage",
        "nested_high_bit_active_blocker",
    ],
)
def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_bogus_proof_content(
    tmp_path,
    mutation,
):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    completed_evidence = _completed_evidence(required_actions)
    if mutation == "missing_proof_source":
        for record in completed_evidence:
            record["evidence"].pop("proof_source")
    elif mutation == "narrow_only_proof_source":
        for record in completed_evidence:
            record["evidence"]["proof_source"] = "return_width_bridge_narrow_query_unsat"
    elif mutation == "summary_proof_source_for_high_bit_query_content":
        for record in completed_evidence:
            record["evidence"]["proof_source"] = (
                "return_width_bridge_narrow_query_unsat_and_summary_parameter_extension"
            )
    elif mutation == "bogus_calling_convention_relation":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "abi_relation_proof":
                evidence["proof_content"]["calling_convention"]["relation"] = (
                    "definitely_not_an_abi_proof"
                )
    elif mutation == "missing_calling_convention_status":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "abi_relation_proof":
                evidence["proof_content"]["calling_convention"].pop("status")
    elif mutation == "bogus_high_bit_proof_label":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "high_bit_proof":
                evidence["proof_content"]["high_bits_irrelevant_or_equal"]["proof"] = (
                    "bogus_proof_label"
                )
    elif mutation == "missing_high_bit_query_stage":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "high_bit_proof":
                evidence["proof_content"]["high_bits_irrelevant_or_equal"].pop("query_stage")
    elif mutation == "bogus_extension_relation":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "high_bit_proof":
                evidence["proof_content"]["extension_semantics"]["relation"] = (
                    "definitely_not_an_extension_proof"
                )
    elif mutation == "missing_extension_status":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "high_bit_proof":
                evidence["proof_content"]["extension_semantics"].pop("status")
    elif mutation == "wrong_extension_policy":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "high_bit_proof":
                evidence["proof_content"]["extension_semantics"]["right_extension"] = (
                    "sign_extend"
                )
    elif mutation == "missing_value_width_evidence":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "high_bit_proof":
                evidence["proof_content"]["producer_width"].pop("value_width_evidence")
    elif mutation == "nested_high_bit_active_blocker":
        for record in completed_evidence:
            evidence = record["evidence"]
            if evidence["proof_kind"] == "high_bit_proof":
                evidence["proof_content"]["high_bits_irrelevant_or_equal"][
                    "active_unsafety_reasons"
                ] = ["sat_unsafety"]
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=completed_evidence,
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert {
        failure["kind"] for failure in gate["entries"][0]["post_fix_failures"]
    } == {"return_width_bridge_completed_proof_required"}


def test_phase3_return_width_bridge_lane2_post_fix_rejects_summary_target_as_high_bit_query_proof(
    tmp_path,
):
    current_payload = _payload(
        reasons=[_width_reason(_target_with_right_summary_parameter_extension())]
    )
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    completed_evidence = _completed_evidence(required_actions)
    for record in completed_evidence:
        evidence = record["evidence"]
        evidence["proof_content"] = CheckStrategy._return_width_bridge_completed_proof_content(
            evidence["proof_kind"],
            CheckStrategy._normalize_nested_tuple(evidence["object_target_key"]),
            query_stage="summary-parameter-extension-object-evidence",
            narrow_width=32,
        )
        evidence["proof_source"] = "return_width_bridge_narrow_and_high_bit_queries_unsat"
        if evidence["proof_kind"] == "high_bit_proof":
            evidence["proof_content"]["high_bits_irrelevant_or_equal"]["proof"] = (
                "high_bits_do_not_affect_compared_return"
            )
            evidence["proof_content"]["high_bits_irrelevant_or_equal"]["query_stage"] = (
                "return-width-bridge-high-bit-extension"
            )

    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=completed_evidence,
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert {
        failure["kind"] for failure in gate["entries"][0]["post_fix_failures"]
    } == {"return_width_bridge_completed_proof_required"}


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_planned_action_backlog(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=required_actions,
            is_equivalent=True,
            completed_evidence=_completed_evidence(required_actions),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert any(
        failure["kind"] == "return_width_bridge_pending_proof_action_still_active"
        for failure in gate["entries"][0]["post_fix_failures"]
    )


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_unknown_action_status(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = pre_fix["entries"][0]["required_completion_actions"]
    stale_actions = json.loads(json.dumps(required_actions))
    stale_actions[0]["status"] = "unexpected_status"
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=stale_actions,
            is_equivalent=True,
            completed_evidence=_completed_evidence(required_actions),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    assert any(
        failure["kind"] == "return_width_bridge_pending_proof_action_still_active"
        for failure in gate["entries"][0]["post_fix_failures"]
    )


def test_phase3_return_width_bridge_lane2_post_fix_rejects_eq_with_partial_completed_proof(tmp_path):
    current_payload = _payload(reasons=[_width_reason(_target())])
    raw_dir, baseline_root, current_root = _setup_logs(tmp_path, current_payload=current_payload)
    pre_fix_path = build_phase3_return_width_bridge_lane2_manifest(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "phase3",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
    )
    pre_fix = json.loads(pre_fix_path.read_text())
    required_actions = [
        action
        for action in pre_fix["entries"][0]["required_completion_actions"]
        if action["proof_stage"] != "high_bit_relation"
    ]
    _write_log(
        current_root,
        _payload(
            reasons=[],
            actions=[],
            is_equivalent=True,
            completed_evidence=_completed_evidence(required_actions),
        ),
    )

    post_fix_path = build_phase3_return_width_bridge_lane2_post_fix_gate(
        baseline_raw_dir=raw_dir,
        output_dir=tmp_path / "gate",
        current_log_roots={"function_call": current_root},
        baseline_log_roots={"function_call": baseline_root},
        phase3_manifest_path=pre_fix_path,
        phase3_manifest_sha256=_sha256_path(pre_fix_path),
    )
    gate = json.loads(post_fix_path.read_text())
    assert gate["phase3_lane2_post_fix_ready"] is False
    assert gate["entries"][0]["post_fix_status"] == "failed"
    failures = gate["entries"][0]["post_fix_failures"]
    assert any(
        failure["kind"] == "return_width_bridge_completed_proof_required"
        and failure["proof_stage"] == "high_bit_relation"
        for failure in failures
    )
    with pytest.raises(ValueError, match="return_width_bridge_post_fix_expected_movement"):
        validate_phase3_return_width_bridge_lane2_post_fix_gate(gate)


def test_phase3_return_width_bridge_lane2_post_fix_cli_requires_sha(capsys):
    with pytest.raises(SystemExit):
        phase3_return_width_bridge_lane2_main(
            [
                "--gate-stage",
                "post-fix",
                "--baseline-raw-dir",
                "raw",
                "--output-dir",
                "out",
                "--current-log-root",
                "function_call=current",
                "--baseline-log-root",
                "function_call=baseline",
            ]
        )
    captured = capsys.readouterr()
    assert "--phase3-manifest-sha256 is required" in captured.err
