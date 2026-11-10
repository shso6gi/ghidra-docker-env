"""Issue #297: recurrence summary の return binding（証拠の型・producer の上限・proof の規則）。

Ghidra を使わない。P-code の事実は ``PcodeDataflowSnapshot`` を直接組み立てて与える（producer が
実 binary で作る写しと同じ型）。正例は「``for (i = 0; i < n; ++i) c += b; return c;``」の形で、
負例はその 1 か所だけを変える。
"""

from __future__ import annotations

from dataclasses import replace
from types import SimpleNamespace
from typing import Any, Dict, List, Optional, Tuple

import pytest

from scripts.function_tracer_pcode.analysis.recurrence import return_binding as producer
from scripts.function_tracer_pcode.analysis.recurrence.models import ResidueLoopCase
from scripts.function_tracer_pcode.analysis.recurrence.summarizer import StructuralRecurrenceSummarizer
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    _runtime_conditions_signature,
    _runtime_expression_signature,
)
from scripts.function_tracer_pcode.core import Condition, Expression, LoopSideEffectProfileRef
from scripts.function_tracer_pcode.core.analysis import ReturnInfo
from scripts.function_tracer_pcode.core.recurrence_contracts import QuarantinedRecurrenceProposal
from scripts.function_tracer_pcode.core.recurrence_return_binding import (
    CountedLoopReturnBindingEvidence,
    CountedUpdateCase,
    PcodeDataflowSnapshot,
    PcodeFactBlock,
    PcodeFactInput,
    PcodeFactOp,
    UpdateCaseCompleteness,
    is_full_pcode_op_key,
    pcode_opcode_is_consistent,
)
from scripts.function_tracer_pcode.core.runtime_refs.pcode import (
    PCODE_MNEMONIC_BY_OPCODE,
    PCODE_OPCODE_BY_MNEMONIC,
)
from scripts.function_tracer_pcode.proof.recurrence_return_binding import (
    RETURN_BINDING_RULES,
    ReturnBindingUnproven,
    validated_return_binding,
)

OPC = PCODE_OPCODE_BY_MNEMONIC
FUNCTION = ("function_identity_v1", "bin", ("function", 1, 0x100), "00000100")
BLOCK_BINARY = "bin"


# ---------------------------------------------------------------------------
# opcode の表
# ---------------------------------------------------------------------------


def test_opcode_table_is_pinned_to_ghidra_12_values():
    assert {name: OPC[name] for name in ("COPY", "RETURN", "CBRANCH", "MULTIEQUAL", "CAST", "POPCOUNT", "LZCOUNT")} == {
        "COPY": 1, "RETURN": 10, "CBRANCH": 5, "MULTIEQUAL": 60, "CAST": 64, "POPCOUNT": 72, "LZCOUNT": 73,
    }
    assert all(PCODE_MNEMONIC_BY_OPCODE[number] == name for name, number in OPC.items())


def test_analysis_opcode_subset_reads_the_core_table():
    from scripts.function_tracer_pcode.analysis.returns._shared import _PCODE_OPCODE_BY_MNEMONIC

    assert all(_PCODE_OPCODE_BY_MNEMONIC[name] == OPC[name] for name in _PCODE_OPCODE_BY_MNEMONIC)


@pytest.mark.parametrize("mnemonic,opcode,expected", [
    ("CAST", 64, True), ("LZCOUNT", 73, True), ("CAST", 73, False), ("LZCOUNT", 64, False),
    ("COPY", 1, True), ("UNREGISTERED_OP", 999, True), ("UNREGISTERED_OP", 64, False),
])
def test_mnemonic_and_opcode_must_agree_in_both_directions(mnemonic, opcode, expected):
    assert pcode_opcode_is_consistent(mnemonic, opcode) is expected


def test_snapshot_rejects_an_op_whose_mnemonic_and_opcode_disagree():
    # 同幅の LZCOUNT を CAST の番号で名乗っても、写しを作れない（CAST として素通りしない）
    with pytest.raises(ValueError, match="inconsistent"):
        PcodeFactOp(_key(0x10, 1, OPC["CAST"]), OPC["CAST"], "LZCOUNT", 3, 4, (PcodeFactInput("free", 4),))


# ---------------------------------------------------------------------------
# 正例の写し・証拠・候補
# ---------------------------------------------------------------------------


def _key(address: int, order: int, opcode: int, ordinal: int = 0) -> Tuple[Any, ...]:
    return (
        "pcode_op", "bin", ("function_entry", "ram", 0x100), ("seq_target", "ram", address),
        address, order, opcode, ordinal,
    )


def _block_key(index: int) -> Tuple[Any, ...]:
    return ("pcode_block", BLOCK_BINARY, ("function_entry", "ram", 0x100), index, ("start", 0x100 + 0x10 * index))


class _Loop:
    """``for (i = start; i < n; i += step) c += b; return c;`` の P-code（変えたい所だけ引数で変える）。"""

    def __init__(
        self, *, step: int = 1, compare: str = "INT_SLESS", return_op: Optional[str] = None,
        counter_via: Optional[str] = None, limit: str = "free", extra_exit: bool = False,
        inner_cycle: bool = False, width: int = 4,
    ) -> None:
        w = width
        self.iv = _key(0x20, 0, OPC["MULTIEQUAL"])
        self.acc = _key(0x20, 1, OPC["MULTIEQUAL"], 1)
        self.cmp = _key(0x24, 2, OPC[compare], 2 if counter_via is None else 3)
        self.cbr = _key(0x28, 3, OPC["CBRANCH"], 3 if counter_via is None else 4)
        self.inext = _key(0x30, 4, OPC["INT_ADD"])
        self.anext = _key(0x34, 5, OPC["INT_ADD"], 1)
        self.limit_def = _key(0x38, 6, OPC[{"header_mult": "INT_MULT", "loop_carried": "MULTIEQUAL",
                                            "load": "LOAD"}.get(limit, "INT_ADD")], 4)
        self.limit_next = _key(0x3c, 10, OPC["INT_SUB"], 2)
        self.ret_copy = _key(0x40, 7, OPC[return_op or "COPY"])
        self.ret = _key(0x44, 8, OPC["RETURN"], 1)
        counter_input = PcodeFactInput("op", w, producer_key=self.iv)
        header_ops = [
            PcodeFactOp(self.iv, OPC["MULTIEQUAL"], "MULTIEQUAL", 1, w, (
                PcodeFactInput("constant", w, constant=0), PcodeFactInput("op", w, producer_key=self.inext))),
            PcodeFactOp(self.acc, OPC["MULTIEQUAL"], "MULTIEQUAL", 1, w, (
                PcodeFactInput("constant", w, constant=0), PcodeFactInput("op", w, producer_key=self.anext))),
        ]
        if counter_via is not None:
            self.via = _key(0x22, 9, OPC[counter_via], 2)
            via_width = 8 if counter_via == "INT_ZEXT" else w
            header_ops.append(PcodeFactOp(self.via, OPC[counter_via], counter_via, 1, via_width, (counter_input,)))
            counter_input = PcodeFactInput("op", via_width, producer_key=self.via)
        size = counter_input.size
        limit_input = (
            PcodeFactInput("free", size) if limit == "free"
            else PcodeFactInput("op", size, producer_key=self.limit_def)
        )
        limit_ops = []
        if limit == "header_mult":      # `while (i < n + n)`: header で毎回計算するが不変
            limit_ops = [PcodeFactOp(self.limit_def, OPC["INT_MULT"], "INT_MULT", 1, size, (
                PcodeFactInput("free", size), PcodeFactInput("constant", size, constant=2)))]
        elif limit == "loop_carried":   # limit が反復ごとに変わる（`n = n - 1`）
            limit_ops = [PcodeFactOp(self.limit_def, OPC["MULTIEQUAL"], "MULTIEQUAL", 1, size, (
                PcodeFactInput("free", size), PcodeFactInput("op", size, producer_key=self.limit_next)))]
        elif limit == "load":           # limit を memory から読む
            limit_ops = [PcodeFactOp(self.limit_def, OPC["LOAD"], "LOAD", 1, size, (
                PcodeFactInput("constant", 8, constant=0), PcodeFactInput("free", 8)))]
        header_ops += limit_ops + [
            PcodeFactOp(self.cmp, OPC[compare], compare, 1, 1, (counter_input, limit_input)),
            PcodeFactOp(self.cbr, OPC["CBRANCH"], "CBRANCH", 1, None, (
                PcodeFactInput("free", 8), PcodeFactInput("op", 1, producer_key=self.cmp))),
        ]
        body_ops = [
            PcodeFactOp(self.inext, OPC["INT_ADD"], "INT_ADD", 2, w, (
                PcodeFactInput("op", w, producer_key=self.iv), PcodeFactInput("constant", w, constant=step % (1 << (8 * w))))),
            PcodeFactOp(self.anext, OPC["INT_ADD"], "INT_ADD", 2, w, (
                PcodeFactInput("op", w, producer_key=self.acc), PcodeFactInput("free", w))),
        ]
        if limit == "loop_carried":
            body_ops.append(PcodeFactOp(self.limit_next, OPC["INT_SUB"], "INT_SUB", 2, size, (
                PcodeFactInput("op", size, producer_key=self.limit_def), PcodeFactInput("constant", size, constant=1))))
        ret_value = PcodeFactInput("op", w, producer_key=self.acc)
        if return_op == "INT_ADD":
            ret_ops = [PcodeFactOp(self.ret_copy, OPC["INT_ADD"], "INT_ADD", 3, w, (
                ret_value, PcodeFactInput("constant", w, constant=1)))]
        else:
            ret_ops = [PcodeFactOp(self.ret_copy, OPC[return_op or "COPY"], return_op or "COPY", 3, w, (ret_value,))]
        ret_ops.append(PcodeFactOp(self.ret, OPC["RETURN"], "RETURN", 3, None, (
            PcodeFactInput("constant", 8, constant=0), PcodeFactInput("op", w, producer_key=self.ret_copy))))
        body_succ = (1, 3) if extra_exit else (1,)
        if inner_cycle:
            body_succ = (1, 4)
        blocks = [
            PcodeFactBlock(0, _block_key(0), (), (1,), None, None, ()),
            PcodeFactBlock(1, _block_key(1), (0, 2), (2, 3), 2, 3, tuple(op.key for op in header_ops)),
            PcodeFactBlock(2, _block_key(2), (1,) + ((4,) if inner_cycle else ()), body_succ,
                           (1 if extra_exit else None), (3 if extra_exit else None),
                           tuple(op.key for op in body_ops)),
            PcodeFactBlock(3, _block_key(3), (1,) + ((2,) if extra_exit else ()), (), None, None,
                           tuple(op.key for op in ret_ops)),
        ]
        if inner_cycle:
            blocks.append(PcodeFactBlock(4, _block_key(4), (2,), (2,), None, None, ()))
        self.snapshot = PcodeDataflowSnapshot(FUNCTION, tuple(blocks), tuple(header_ops + body_ops + ret_ops))


def _summarizer():
    return StructuralRecurrenceSummarizer(None)


N = Expression.parameter("param_1", index=0, size=4)
B = Expression.parameter("param_2", index=1, size=4)
ZERO = Expression.constant(0, size=4)
IV = Expression.parameter("__loop_iv", index=-10_000, size=4)
ACC = Expression.variable("__loop_acc", size=4)


def _cond(negated: bool, left=ZERO, right=N, operator="INT_SLESS") -> Condition:
    expr = Expression.binary_op(operator, left, right)
    expr.size = 1
    return Condition(expr, negated)


def _update_case(update=None, conditions=()) -> CountedUpdateCase:
    update = update if update is not None else Expression.binary_op("INT_ADD", ACC, B)
    update.size = 4
    return CountedUpdateCase(
        conditions=tuple(conditions), update_expression=update,
        conditions_signature=_runtime_conditions_signature(list(conditions)),
        update_signature=_runtime_expression_signature(update),
    )


def _evidence(loop: _Loop, **changes) -> CountedLoopReturnBindingEvidence:
    fields: Dict[str, Any] = dict(
        function_identity=FUNCTION, snapshot=loop.snapshot,
        accumulator_phi_key=loop.acc, induction_phi_key=loop.iv,
        start_expression=ZERO, limit_expression=N, initial_expression=ZERO,
        induction_placeholder=IV, accumulator_placeholder=ACC,
        start_signature=_runtime_expression_signature(ZERO),
        limit_signature=_runtime_expression_signature(N),
        initial_signature=_runtime_expression_signature(ZERO),
        update_cases=(_update_case(),), completeness=UpdateCaseCompleteness(),
    )
    fields.update(changes)
    return CountedLoopReturnBindingEvidence(**fields)


def _loop_value(*, step=1, signed=True, bias=B, residue=(1, 0, 0, 0), start=ZERO, limit=N, base=ZERO):
    return _summarizer()._build_counted_loop_summary_value(
        base_expr=base, start_expr=start, limit_expr=limit, induction_step=step,
        residue_cases=(ResidueLoopCase(residue[0], residue[1], (residue[2], residue[3]), bias_expr=bias),),
        result_size=4, signed_loop=signed,
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_scalar_loop"),
        guard_constraints=[_cond(False)], cases=(),
    )


def _profile(snapshot: PcodeDataflowSnapshot, **changes):
    edges = tuple(
        (block.key, snapshot.block(successor).key)
        for block in snapshot.blocks for successor in block.successors
    )
    fields = dict(
        pcode_enumeration_complete=True, cfg_edges_complete=True, terminal_return_coverage_complete=True,
        region_pcode_op_keys=tuple(op.key for op in snapshot.ops), pcode_op_count=len(snapshot.ops),
        region_cfg_edge_keys=edges,
        return_block_count=len(snapshot.ops_with_opcode(OPC["RETURN"])),
    )
    fields.update(changes)
    return SimpleNamespace(**fields)


class _Case:
    """proof の入力 1 組（解析・proposal・候補）。変えたいものだけ置き換える。"""

    def __init__(self, loop: Optional[_Loop] = None, *, evidence=None, loop_value=None, base_value=ZERO,
                 loop_guard=None, base_guard=None, raw_returns=None, profile=None, digest=None,
                 kind="counted_loop_transition_evidence", candidate_evidence=None) -> None:
        loop = loop or _Loop()
        self.loop = loop
        evidence = evidence or _evidence(loop)
        tkey = (kind, ("accumulator_phi", loop.acc), ("header_block", _block_key(1)))
        carried = None if candidate_evidence is False else (candidate_evidence if candidate_evidence is not None else evidence)
        base_info = ReturnInfo(address="0x44", value=base_value, conditions=[base_guard or _cond(True)],
                               summary_transition_evidence_key=tkey, summary_return_binding_evidence=carried)
        loop_info = ReturnInfo(address="0x44", value=loop_value if loop_value is not None else _loop_value(),
                               conditions=[loop_guard or _cond(False)],
                               summary_transition_evidence_key=tkey, summary_return_binding_evidence=carried)
        self.candidates = (
            SimpleNamespace(candidate_id=("c", 0), transition_evidence_key=tkey, return_info=base_info),
            SimpleNamespace(candidate_id=("c", 1), transition_evidence_key=tkey, return_info=loop_info),
        )
        self.proposal = SimpleNamespace(
            new_returns=(SimpleNamespace(candidate_id=("c", 0)), SimpleNamespace(candidate_id=("c", 1))),
            return_binding_evidence=evidence, digest="proposal-digest",
        )
        raw = raw_returns if raw_returns is not None else [
            ReturnInfo(address="0x44", value=ZERO, conditions=[_cond(True)]),
            ReturnInfo(address="0x44", value=Expression.unknown("phi_circular"), conditions=[_cond(False)]),
        ]
        self.analysis = SimpleNamespace(
            outcome_function_identity=lambda: FUNCTION,
            pcode_dataflow_digest=digest if digest is not None else loop.snapshot.digest,
            effect_summary=SimpleNamespace(function_control_effect_profile=profile or _profile(loop.snapshot)),
            returns=raw,
        )

    def run(self):
        return validated_return_binding(self.analysis, self.proposal, self.candidates)

    def failures(self) -> Tuple[str, ...]:
        with pytest.raises(ReturnBindingUnproven) as info:
            self.run()
        return info.value.failures


def _rules(failures) -> set:
    return {item.split(":")[0] for item in failures}


def test_copy_bound_counted_loop_is_proved_and_names_every_rule():
    proposition = _Case().run()
    assert proposition[0] == "return_binding_v1"
    assert proposition[4] == RETURN_BINDING_RULES
    assert set(proposition[3]) == {("c", 0), ("c", 1)}


# ---------------------------------------------------------------------------
# R / B2: RETURN の値は accumulator PHI そのもの（COPY だけ）
# ---------------------------------------------------------------------------


def test_return_of_accumulator_plus_one_is_not_bound():
    # UnchLoop new の形（`return c + 1`）: zero-trip の一致（Z）では検出できない場合も R で拒否する
    failures = _Case(_Loop(return_op="INT_ADD")).failures()
    assert "R:blocked_by:INT_ADD/4" in failures


def test_same_width_lzcount_on_the_return_chain_is_not_bound():
    failures = _Case(_Loop(return_op="LZCOUNT")).failures()
    assert "R:blocked_by:LZCOUNT/4" in failures


def test_cast_on_the_return_chain_is_not_bound_in_the_first_pr():
    failures = _Case(_Loop(return_op="CAST")).failures()
    assert "R:blocked_by:CAST/4" in failures


def test_candidate_width_must_match_the_return_width():
    failures = _Case(base_value=Expression.constant(0, size=8)).failures()
    assert "B2:candidate_width" in failures


# ---------------------------------------------------------------------------
# T / X2 / T6: 停止と回数（wrap・非停止の形を拒否する）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("loop,expected", [
    (_Loop(step=2), "T:form:iv<L/(2,)"),                       # 32 bit の counter を 2 ずつ（w9 の形）
    (_Loop(compare="INT_SLESSEQUAL"), "T:form:iv<=L/(1,)"),    # `<=`（limit = MAX で 0 回に化ける）
    (_Loop(compare="INT_NOTEQUAL"), "T:guard_op:INT_NOTEQUAL"),
    (_Loop(counter_via="INT_ZEXT"), "T:guard_counter_operand_not_unique_or_cast"),  # w8 の形
    (_Loop(limit="loop_carried"), "T:limit_not_loop_invariant"),  # T-inv の不成立（反復ごとに変わる）
    (_Loop(limit="load"), "T:limit_not_loop_invariant"),          # T-inv の不成立（memory から読む）
])
def test_wrapping_or_non_terminating_loop_forms_are_rejected(loop, expected):
    assert expected in _Case(loop).failures()


def test_same_width_cast_on_the_counter_keeps_the_counter_identity():
    # r1_residue の形: 比較の operand が同幅の CAST を通る（signedness は比較の opcode が決める）
    assert _Case(_Loop(counter_via="CAST")).run()[0] == "return_binding_v1"


@pytest.mark.parametrize("limit", ["free", "header_mult"])
def test_loop_invariant_limit_is_accepted(limit):
    # T-inv の成立: limit が関数の入力、または不変な入力の純粋な整数演算（REVE/loop5 の `n + n`）
    assert _Case(_Loop(limit=limit)).run()[0] == "return_binding_v1"


def test_second_loop_exit_is_rejected():
    assert any(item.startswith("X2:") for item in _Case(_Loop(extra_exit=True)).failures())


def test_inner_cycle_is_rejected():
    assert "T6:inner_cycle" in _Case(_Loop(inner_cycle=True)).failures()


# ---------------------------------------------------------------------------
# C / E / G / Z: 候補の値と P-code の事実の不一致
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("value,expected", [
    (dict(step=2), "C:step"),
    (dict(signed=False), "C:signed"),
    (dict(start=Expression.constant(1, size=4)), "C:start"),
    (dict(limit=Expression.binary_op("INT_ADD", N, Expression.constant(1, size=4))), "C:limit"),
    (dict(base=Expression.constant(1, size=4)), "C:loop_base"),
])
def test_candidate_fields_must_match_the_pcode_facts(value, expected):
    assert expected in _Case(loop_value=_loop_value(**value)).failures()


def test_base_value_must_be_the_accumulator_initial_value():
    assert "C:base_value" in _Case(base_value=Expression.constant(1, size=4)).failures()


def test_guards_must_be_the_entry_comparison():
    other = _cond(False, ZERO, B)
    failures = _Case(loop_guard=other, base_guard=_cond(True, ZERO, B)).failures()
    assert {"G:loop_guard", "G:base_guard"} <= set(failures)


def test_zero_trip_needs_an_equal_raw_exact_return():
    raw = [ReturnInfo(address="0x44", value=Expression.constant(1, size=4), conditions=[_cond(True)])]
    assert "Z:refuted_or_unknown" in _Case(raw_returns=raw).failures()
    unknown_only = [ReturnInfo(address="0x44", value=Expression.unknown("x"), conditions=[_cond(True)])]
    assert "Z:no_equivalent_exact_raw_return" in _Case(raw_returns=unknown_only).failures()


# ---------------------------------------------------------------------------
# U / U0: 更新 case の完全性と、residue / bias の対応
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("completeness,expected", [
    (UpdateCaseCompleteness(path_enumeration_truncated=True), "U:path_enumeration_truncated"),
    (UpdateCaseCompleteness(unknown_branch_conditions=1), "U:branch_condition_unknown"),
    (UpdateCaseCompleteness(unresolved_update_inputs=1), "U:update_input_unresolved"),
    (UpdateCaseCompleteness(delta_extraction_failures=1), "U:delta_extraction_failed"),
    (UpdateCaseCompleteness(uncovered_backedge_targets=(2,)), "U:backedge_uncovered"),
    (UpdateCaseCompleteness(update_varnode_with_multiple_backedges=True), "U:update_varnode_with_multiple_backedges"),
])
def test_any_dropped_update_path_rejects_even_when_the_remaining_cases_look_total(completeness, expected):
    # 残った case は条件なし（論理和は自明に真）で、更新式も正しい。それでも落としたものがあれば拒否する
    loop = _Loop()
    assert expected in _Case(loop, evidence=_evidence(loop, completeness=completeness)).failures()


def test_complete_extraction_with_every_backedge_covered_is_accepted():
    loop = _Loop()
    assert _Case(loop, evidence=_evidence(loop, completeness=UpdateCaseCompleteness())).run()


def test_bias_term_must_match_the_extracted_update():
    plus_one = Expression.binary_op("INT_ADD", B, Expression.constant(1, size=4))
    plus_one.size = 4
    assert "U:update_mismatch" in _Case(loop_value=_loop_value(bias=plus_one)).failures()


def test_residue_coefficient_must_match_the_extracted_update():
    assert "U:update_mismatch" in _Case(loop_value=_loop_value(residue=(1, 0, 0, 1))).failures()


def test_case_without_residue_condition_cannot_stand_for_a_residue_split():
    loop = _Loop()
    value = _summarizer()._build_counted_loop_summary_value(
        base_expr=ZERO, start_expr=ZERO, limit_expr=N, induction_step=1,
        residue_cases=(ResidueLoopCase(2, 0, (0, 0), bias_expr=B), ResidueLoopCase(2, 1, (0, 0), bias_expr=B)),
        result_size=4, signed_loop=True,
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_scalar_loop"),
        guard_constraints=[_cond(False)], cases=(),
    )
    assert "U:case_residue_unknown" in _Case(loop, loop_value=value).failures()


# ---------------------------------------------------------------------------
# KIND / EV / R-census: 種類・出所・census
# ---------------------------------------------------------------------------


def test_other_summary_kinds_are_rejected():
    assert _rules(_Case(kind="state_transition_loop_evidence").failures()) == {"KIND"}


def test_missing_evidence_is_rejected():
    case = _Case()
    case.proposal.return_binding_evidence = None
    assert case.failures() == ("EV:missing",)


def test_evidence_from_another_analysis_is_rejected():
    # op の key と CFG が同じでも、写しの digest が現在の解析のものでなければ使わない
    assert "EV:pcode_source" in _Case(digest="0" * 64).failures()


def test_only_the_proposal_carries_the_evidence():
    # 候補の ReturnInfo は証拠を運ばない（解析の successor・比較の case として写されるため）。proposal の証拠で判定する
    assert _Case(candidate_evidence=False).run()[0] == "return_binding_v1"


def test_attach_moves_the_evidence_onto_the_proposal_only():
    from scripts.function_tracer_pcode.analysis.returns.summary_returns import _shared_return_binding_evidence

    loop = _Loop()
    evidence = _evidence(loop)
    with_evidence = [ReturnInfo(address="0x44", value=ZERO, conditions=[_cond(True)],
                                summary_return_binding_evidence=evidence) for _ in range(2)]
    assert _shared_return_binding_evidence(with_evidence) is evidence
    other = _evidence(loop, initial_signature=("other",))
    mixed = [with_evidence[0], replace(with_evidence[1], summary_return_binding_evidence=other)]
    assert _shared_return_binding_evidence(mixed) is None
    assert _shared_return_binding_evidence([replace(with_evidence[0], summary_return_binding_evidence=None)]) is None


def test_producer_failure_is_rejected():
    loop = _Loop()
    case = _Case(loop, evidence=_evidence(loop, producer_failures=("scan_bound_exceeded",)))
    assert "EV:producer:scan_bound_exceeded" in case.failures()


def test_function_identity_must_match():
    case = _Case()
    case.analysis.outcome_function_identity = lambda: ("function_identity_v1", "other", ("function", 1, 0x200), "200")
    assert "EV:function_identity" in case.failures()


@pytest.mark.parametrize("mutate,expected", [
    (lambda keys: keys + (("pcode_op", None, 1, 2, 3, "COPY"),), "R-census:fallback_key"),
    (lambda keys: keys + (keys[0],), "R-census:duplicate_key"),
    (lambda keys: keys[:-1], "R-census:op_keys"),
])
def test_census_with_fallback_duplicate_or_missing_keys_is_rejected(mutate, expected):
    loop = _Loop()
    keys = tuple(op.key for op in loop.snapshot.ops)
    profile = _profile(loop.snapshot, region_pcode_op_keys=mutate(keys))
    assert expected in _Case(loop, profile=profile).failures()


def test_census_cfg_edges_must_match_the_snapshot():
    loop = _Loop()
    profile = _profile(loop.snapshot, region_cfg_edge_keys=())
    assert "R-census:cfg_edges" in _Case(loop, profile=profile).failures()


def test_fallback_key_is_not_a_full_op_key():
    assert not is_full_pcode_op_key(("pcode_op", 0x10, 1, 2, 3, "COPY"))
    assert is_full_pcode_op_key(_key(0x10, 1, OPC["COPY"]))


def test_snapshot_rejects_inconsistent_shapes():
    loop = _Loop()
    with pytest.raises(ValueError, match="duplicate op key"):
        PcodeDataflowSnapshot(FUNCTION, loop.snapshot.blocks, loop.snapshot.ops + (loop.snapshot.ops[0],))
    with pytest.raises(ValueError, match="unknown op"):
        dangling = PcodeFactOp(_key(0x50, 9, OPC["COPY"]), OPC["COPY"], "COPY", 0, 4,
                               (PcodeFactInput("op", 4, producer_key=_key(0x99, 9, OPC["COPY"])),))
        blocks = (replace(loop.snapshot.blocks[0], op_keys=(dangling.key,)),) + loop.snapshot.blocks[1:]
        PcodeDataflowSnapshot(FUNCTION, blocks, loop.snapshot.ops + (dangling,))


def test_evidence_digest_is_part_of_the_proposal_digest():
    loop = _Loop()
    one = QuarantinedRecurrenceProposal("s" * 64, "counted_scalar_loop_summary", (), (),
                                        return_binding_evidence=_evidence(loop))
    other = QuarantinedRecurrenceProposal("s" * 64, "counted_scalar_loop_summary", (), (),
                                          return_binding_evidence=_evidence(loop, initial_signature=("x",)))
    none = QuarantinedRecurrenceProposal("s" * 64, "counted_scalar_loop_summary", (), ())
    assert len({one.digest, other.digest, none.digest}) == 3


# ---------------------------------------------------------------------------
# producer: 写しの走査の上限（記録の足りない iterator で回り続けない）
# ---------------------------------------------------------------------------


class _EndlessIterator:
    def __init__(self, item) -> None:
        self.item = item

    def hasNext(self) -> bool:
        return True

    def next(self):
        return self.item


class _Block:
    def __init__(self, ops_iterator) -> None:
        self._ops_iterator = ops_iterator

    def getIterator(self):
        return self._ops_iterator


def test_snapshot_capture_stops_at_the_census_bound_on_an_endless_iterator(monkeypatch):
    profile = SimpleNamespace(block_count=2, pcode_op_count=5)
    analysis = SimpleNamespace(
        effect_summary=SimpleNamespace(function_control_effect_profile=profile),
        outcome_function_identity=lambda: FUNCTION,
    )
    high_function = SimpleNamespace(getBasicBlocks=lambda: [_Block(_EndlessIterator(object()))])
    counter = {"n": 0}

    def fake_ref(_op, **_kwargs):
        counter["n"] += 1
        n = counter["n"]
        return SimpleNamespace(_has_full_identity_context=lambda: True,
                               stable_key=lambda: _key(0x10 + n, n, OPC["COPY"]))

    # 記録の足りない iterator は同じ op を返し続ける。identity は毎回新しく見えても、上限で止まること
    monkeypatch.setattr(producer.PcodeOpRef, "from_pcode_op", staticmethod(fake_ref))
    monkeypatch.setattr(producer, "_seq_identity", lambda _op: ("ram", counter["n"], 0, 0))
    summarizer = StructuralRecurrenceSummarizer(SimpleNamespace())
    snapshot, live, failure = summarizer._capture_pcode_dataflow_snapshot(high_function, analysis)
    assert snapshot is None and live == {}
    assert failure == "scan_bound_exceeded"
    assert counter["n"] <= profile.pcode_op_count


def test_snapshot_capture_needs_the_census():
    analysis = SimpleNamespace(effect_summary=None, outcome_function_identity=lambda: FUNCTION)
    summarizer = StructuralRecurrenceSummarizer(SimpleNamespace())
    assert summarizer._capture_pcode_dataflow_snapshot(SimpleNamespace(), analysis) == (None, {}, "census_unavailable")


def test_endless_block_list_is_also_bounded():
    profile = SimpleNamespace(block_count=3, pcode_op_count=3)
    analysis = SimpleNamespace(
        effect_summary=SimpleNamespace(function_control_effect_profile=profile),
        outcome_function_identity=lambda: FUNCTION,
    )

    class _EndlessList:
        def iterator(self):
            return _EndlessIterator(_Block(_EndlessIterator(object())))

    summarizer = StructuralRecurrenceSummarizer(SimpleNamespace())
    snapshot, _live, failure = summarizer._capture_pcode_dataflow_snapshot(
        SimpleNamespace(getBasicBlocks=lambda: _EndlessList()), analysis,
    )
    assert snapshot is None and failure == "scan_bound_exceeded"


# ---------------------------------------------------------------------------
# 経路の列挙: 条件の取れない分岐の辺を数える（落ちた経路を覆ったことにしない）
# ---------------------------------------------------------------------------


class _CfgBlock:
    def __init__(self, name: str) -> None:
        self.name = name
        self.successors: List["_CfgBlock"] = []


def _enumerator(edge_condition):
    summarizer = StructuralRecurrenceSummarizer(SimpleNamespace())
    summarizer._block_key = lambda block: None if block is None else block.name
    summarizer._collect_block_successors = lambda block: list(block.successors)
    summarizer._build_block_edge_condition = lambda block, successor, **_kw: edge_condition(block, successor)
    return summarizer


def _diamond():
    body, then, other, latch, header, exit_block = (_CfgBlock(n) for n in ("body", "then", "else", "latch", "header", "exit"))
    body.successors = [then, other]
    then.successors = [latch]
    other.successors = [latch]
    latch.successors = [header]
    return body, latch, header, exit_block


def test_enumeration_report_counts_unknown_branch_conditions():
    body, latch, header, exit_block = _diamond()
    summarizer = _enumerator(lambda block, successor: None)
    paths, truncated, unknown = summarizer._enumerate_paths_with_conditions_report(
        start_block=body, target_block=latch, header_block=header, placeholders={}, stop_block=exit_block,
    )
    assert len(paths) == 2 and not truncated
    assert unknown == 2                     # 2 分岐の両方の辺で条件が無い
    assert summarizer._enumerate_paths_with_conditions_result(
        start_block=body, target_block=latch, header_block=header, placeholders={}, stop_block=exit_block,
    ) == (paths, False)                     # 既存の呼び出しの戻り値は変わらない


def test_enumeration_report_has_no_unknown_edges_when_conditions_exist():
    body, latch, header, exit_block = _diamond()
    known = _cond(False)
    summarizer = _enumerator(lambda block, successor: known if block.name == "body" else None)
    _paths, _truncated, unknown = summarizer._enumerate_paths_with_conditions_report(
        start_block=body, target_block=latch, header_block=header, placeholders={}, stop_block=exit_block,
    )
    assert unknown == 0                     # 1 本道の辺（後続が 1 つ）は数えない


# ---------------------------------------------------------------------------
# 更新 case の抽出: 落としたものを数える（成立・不成立の両方）
# ---------------------------------------------------------------------------


class _Varnode:
    def __init__(self, name: str, definition=None) -> None:
        self.name = name
        self._definition = definition

    def getDef(self):
        return self._definition


class _PhiBlock:
    def __init__(self, index: int, predecessors) -> None:
        self.index = index
        self.predecessors = list(predecessors)

    def getIndex(self):
        return self.index

    def getInSize(self):
        return len(self.predecessors)

    def getIn(self, position):
        return self.predecessors[position]


class _Phi:
    def __init__(self, parent, inputs) -> None:
        self.parent = parent
        self.inputs = list(inputs)

    def getParent(self):
        return self.parent

    def getInput(self, position):
        return self.inputs[position]

    def getNumInputs(self):
        return len(self.inputs)

    def getMnemonic(self):
        return "MULTIEQUAL"


def _extraction(*, unresolved=(), no_delta=(), unreachable=(), update_varnode=False, backedges=(1, 2), legacy=False):
    from scripts.function_tracer_pcode.analysis.recurrence.models import (
        CountedLoopAccumulator, CountedLoopGuard, CountedLoopInduction,
    )

    entry, latch_a, latch_b = _PhiBlock(0, ()), _PhiBlock(5, ()), _PhiBlock(6, ())
    header = _PhiBlock(1, (entry, latch_a, latch_b))
    values = {name: _Varnode(name) for name in ("init", "a", "b")}
    acc_phi = _Phi(header, (values["init"], values["a"], values["b"]))
    iv_phi = _Phi(header, (values["init"], values["a"], values["b"]))
    accumulator = CountedLoopAccumulator(
        phi_op=acc_phi, phi_output=_Varnode("acc"), init_expr=ZERO, backedge_index=1, placeholder=ACC,
        member_outputs=(), member_placeholders=(), backedge_indices=tuple(backedges),
        update_varnode=_Varnode("u") if update_varnode else None, update_block=latch_a if update_varnode else None,
    )
    induction = CountedLoopInduction(
        phi_op=iv_phi, phi_output=_Varnode("iv"), init_expr=ZERO, backedge_index=1, step=1,
        placeholder=IV, signed_guard=False, backedge_indices=tuple(backedges),
    )
    guard = CountedLoopGuard(
        condition_expr=_cond(False).expression, bound_expr=N, continue_on_true=True,
        body_block=_PhiBlock(2, ()), exit_block=_PhiBlock(3, ()), signed_comparison=True,
    )
    summarizer = StructuralRecurrenceSummarizer(SimpleNamespace())
    summarizer._collect_affine_loop_state_placeholders = lambda **_kw: {}
    expressions = {
        "a": Expression.binary_op("INT_ADD", ACC, B), "b": Expression.binary_op("INT_ADD", ACC, B),
        "u": Expression.binary_op("INT_ADD", ACC, B),
    }
    summarizer._build_pcode_expression = lambda varnode, **_kw: (
        Expression.unknown("unresolved") if varnode.name in unresolved else expressions[varnode.name]
    )
    summarizer._enumerate_paths_with_conditions_report = lambda *, target_block, **_kw: (
        ([], False, 0) if target_block.index in unreachable else ([[]], False, 0)
    )
    original_delta = summarizer._extract_additive_delta
    summarizer._extract_additive_delta = lambda update, acc, conditions: (
        None if any(update is expressions[name] for name in no_delta) else original_delta(update, acc, conditions)
    )
    if legacy:
        return (
            summarizer._extract_counted_loop_update_cases(accumulator, induction, guard),
            summarizer._extract_counted_loop_update_cases_with_completeness(accumulator, induction, guard),
        )
    return summarizer._extract_counted_loop_update_cases_with_completeness(accumulator, induction, guard)


def test_extraction_with_every_input_resolved_is_complete():
    cases, completeness = _extraction()
    assert cases and completeness.is_complete


def test_extraction_counts_an_unresolved_backedge_input():
    _cases, completeness = _extraction(unresolved=("b",))
    assert completeness.unresolved_update_inputs == 1
    assert "update_input_unresolved" in completeness.failures()


def test_extraction_counts_a_failed_delta():
    _cases, completeness = _extraction(no_delta=("b",))
    assert completeness.delta_extraction_failures == 1
    assert "delta_extraction_failed" in completeness.failures()


def test_extraction_reports_a_backedge_with_no_path_from_the_body():
    # U0 の不成立: latch の 1 つへ本体から経路が無い（そこからの更新は 1 つも case にならない）
    _cases, completeness = _extraction(unreachable=(6,))
    assert completeness.uncovered_backedge_targets == (6,)
    assert "backedge_uncovered" in completeness.failures()


def test_extraction_rejects_update_varnode_with_several_backedges():
    _cases, completeness = _extraction(update_varnode=True, backedges=(1, 2))
    assert completeness.update_varnode_with_multiple_backedges
    _cases, single = _extraction(update_varnode=True, backedges=(1,))
    assert single.is_complete


def test_legacy_extraction_returns_the_same_cases():
    # 既存の呼び出し（model の抽出）は、完全性の記録を足す前と同じ case を受け取る
    legacy, (cases, _completeness) = _extraction(no_delta=("b",), legacy=True)
    assert isinstance(legacy, list) and tuple(legacy) == cases


def test_analysis_successor_copies_the_evidence_it_carries():
    # 解析の successor は ReturnInfo・候補を field ごとに写す。証拠を載せた解析も写せ、写しの digest は同じ
    from scripts.function_tracer_pcode.core.analysis import _semantic_copy

    evidence = _evidence(_Loop())
    copied = _semantic_copy(evidence)
    assert copied.digest == evidence.digest
    assert copied.snapshot.op(evidence.accumulator_phi_key) is not None
    info = ReturnInfo(address="0x44", value=ZERO, conditions=[_cond(True)], summary_return_binding_evidence=evidence)
    assert _semantic_copy(info).summary_return_binding_evidence.digest == evidence.digest
