"""Issue #297: recurrence summary の return binding（証拠の型・producer の上限・proof の規則）。

Ghidra を使わない。P-code の事実は ``PcodeDataflowSnapshot`` を直接組み立てて与える（producer が
実 binary で作る写しと同じ型）。正例は「``for (i = 0; i < n; ++i) c += b; return c;``」の形で、
負例はその 1 か所だけを変える。

値の意味（start・limit・初期値・1 回分の更新）は proof が写しから作る。producer（builder・tracer）の
式は証拠に入らないので、写しと候補が食い違えば、producer の式が候補と一致していても拒否する。
"""

from __future__ import annotations

import copy
from dataclasses import replace
from types import SimpleNamespace
from typing import Any, Optional, Tuple

import pytest

from scripts.function_tracer_pcode.analysis.recurrence import return_binding as producer
from scripts.function_tracer_pcode.analysis.recurrence import value_queries
from scripts.function_tracer_pcode.analysis.recurrence.models import ResidueLoopCase
from scripts.function_tracer_pcode.analysis.recurrence.summarizer import StructuralRecurrenceSummarizer
from scripts.function_tracer_pcode.core import Condition, Expression, LoopSideEffectProfileRef
from scripts.function_tracer_pcode.core.analysis import ReturnInfo
from scripts.function_tracer_pcode.core.recurrence_contracts import (
    RETURN_BINDING_PROPOSITION,
    QuarantinedRecurrenceProposal,
    RecurrenceSubproofEvidence,
)
from scripts.function_tracer_pcode.core.recurrence_return_binding import (
    CountedLoopReturnBindingEvidence,
    PcodeDataflowSnapshot,
    PcodeFactBlock,
    PcodeFactInput,
    PcodeFactOp,
    is_full_pcode_op_key,
    loop_region,
    pcode_opcode_is_consistent,
    return_binding_proposition,
    validate_return_binding_subproof,
)
from scripts.function_tracer_pcode.core.runtime_refs.pcode import (
    PCODE_MNEMONIC_BY_OPCODE,
    PCODE_OPCODE_BY_MNEMONIC,
)
from scripts.function_tracer_pcode.proof.recurrence_pcode_semantics import LoweringFailure, SnapshotLowering
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
        PcodeFactOp(_key(0x10, 1, OPC["CAST"]), OPC["CAST"], "LZCOUNT", 3, 4, (_param(1),))


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


def _param(index: int, size: int = 4) -> PcodeFactInput:
    """関数の引数 ``index`` の入力（arm64 の引数 register の置き場所）。"""

    return PcodeFactInput("free", size, storage=("register", 0x4000 + 8 * index), parameter_index=index)


def _target(address: int) -> PcodeFactInput:
    """BRANCH / CBRANCH の分岐先（値ではない address の入力）。"""

    return PcodeFactInput("free", 8, storage=("ram", address))


def _const(value: int, size: int = 4) -> PcodeFactInput:
    return PcodeFactInput("constant", size, constant=value % (1 << (8 * size)))


def _op(key, size=4) -> PcodeFactInput:
    return PcodeFactInput("op", size, producer_key=key)


class _Loop:
    """``for (i = start; i < n; i += step) c = <update>; return c;`` の P-code（変えたい所だけ引数で変える）。

    ``update``: ``"param"``（``c + b``）・``"const7"``（``c + 7``）・``"lzcount"``（``c + LZCOUNT(b)``）・
    ``"load"``（``c + *p``）・``"nonparam"``（``c + 引数でない入力``）・``"residue"``（``if ((i & 1) == 0)
    c += 1; else c += b;`` の body の分岐）・``"residue_load"``（分岐の条件を memory から読む）。
    ``init``: ``"zero"``・``"lzcount"``（``c = LZCOUNT(b)``）。
    """

    def __init__(
        self, *, step: int = 1, compare: str = "INT_SLESS", return_op: Optional[str] = None,
        counter_via: Optional[str] = None, limit: str = "free", extra_exit: bool = False,
        inner_cycle: bool = False, width: int = 4, update: str = "param", init: str = "zero",
        start: int = 0, b_parameter: int = 1,
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
        b = _param(b_parameter, w)
        init_ops = []
        init_input = _const(0, w)
        if init == "lzcount":
            self.init_def = _key(0x12, 20, OPC["LZCOUNT"])
            init_ops = [PcodeFactOp(self.init_def, OPC["LZCOUNT"], "LZCOUNT", 0, w, (b,))]
            init_input = _op(self.init_def, w)
        counter_input = _op(self.iv, w)
        header_ops = [
            PcodeFactOp(self.iv, OPC["MULTIEQUAL"], "MULTIEQUAL", 1, w, (_const(start, w), _op(self.inext, w))),
            PcodeFactOp(self.acc, OPC["MULTIEQUAL"], "MULTIEQUAL", 1, w, (init_input, init_input)),
        ]
        if counter_via is not None:
            self.via = _key(0x22, 9, OPC[counter_via], 2)
            via_width = 8 if counter_via == "INT_ZEXT" else w
            header_ops.append(PcodeFactOp(self.via, OPC[counter_via], counter_via, 1, via_width, (counter_input,)))
            counter_input = _op(self.via, via_width)
        size = counter_input.size
        limit_input = _param(0, size) if limit == "free" else _op(self.limit_def, size)
        limit_ops = []
        if limit == "header_mult":      # `while (i < n + n)`: header で毎回計算するが不変
            limit_ops = [PcodeFactOp(self.limit_def, OPC["INT_MULT"], "INT_MULT", 1, size, (
                _param(0, size), _const(2, size)))]
        elif limit == "loop_carried":   # limit が反復ごとに変わる（`n = n - 1`）
            limit_ops = [PcodeFactOp(self.limit_def, OPC["MULTIEQUAL"], "MULTIEQUAL", 1, size, (
                _param(0, size), _op(self.limit_next, size)))]
        elif limit == "load":           # limit を memory から読む
            limit_ops = [PcodeFactOp(self.limit_def, OPC["LOAD"], "LOAD", 1, size, (
                _const(0, 8), _param(2, 8)))]
        header_ops += limit_ops + [
            PcodeFactOp(self.cmp, OPC[compare], compare, 1, 1, (counter_input, limit_input)),
            PcodeFactOp(self.cbr, OPC["CBRANCH"], "CBRANCH", 1, None, (_target(0x80), _op(self.cmp, 1))),
        ]
        body_blocks = []
        latch = 2
        if update in {"residue", "residue_load"}:
            # block 2: `if ((i & 1) == 0)` → 4（c + 1）/ 5（c + b）→ 6（合流して header へ）
            self.mask = _key(0x50, 11, OPC["INT_AND"])
            self.test = _key(0x54, 12, OPC["INT_EQUAL"] if update == "residue" else OPC["LOAD"])
            self.bcb = _key(0x58, 13, OPC["CBRANCH"])
            self.even = _key(0x5c, 14, OPC["INT_ADD"])
            self.odd = _key(0x60, 15, OPC["INT_ADD"])
            self.join = _key(0x64, 16, OPC["MULTIEQUAL"])
            test_op = (
                PcodeFactOp(self.test, OPC["INT_EQUAL"], "INT_EQUAL", 2, 1, (_op(self.mask, w), _const(0, w)))
                if update == "residue"
                else PcodeFactOp(self.test, OPC["LOAD"], "LOAD", 2, 1, (_const(0, 8), _param(2, 8)))
            )
            block2 = [
                PcodeFactOp(self.inext, OPC["INT_ADD"], "INT_ADD", 2, w, (_op(self.iv, w), _const(step, w))),
                PcodeFactOp(self.mask, OPC["INT_AND"], "INT_AND", 2, w, (_op(self.iv, w), _const(1, w))),
                test_op,
                PcodeFactOp(self.bcb, OPC["CBRANCH"], "CBRANCH", 2, None, (_target(0x90), _op(self.test, 1))),
            ]
            block4 = [PcodeFactOp(self.even, OPC["INT_ADD"], "INT_ADD", 4, w, (_op(self.acc, w), _const(1, w)))]
            block5 = [PcodeFactOp(self.odd, OPC["INT_ADD"], "INT_ADD", 5, w, (_op(self.acc, w), b))]
            block6 = [PcodeFactOp(self.join, OPC["MULTIEQUAL"], "MULTIEQUAL", 6, w, (_op(self.even, w), _op(self.odd, w)))]
            body_blocks = [
                PcodeFactBlock(2, _block_key(2), (1,), (4, 5), 4, 5, tuple(op.key for op in block2)),
                PcodeFactBlock(4, _block_key(4), (2,), (6,), None, None, tuple(op.key for op in block4)),
                PcodeFactBlock(5, _block_key(5), (2,), (6,), None, None, tuple(op.key for op in block5)),
                PcodeFactBlock(6, _block_key(6), (4, 5), (1,), None, None, tuple(op.key for op in block6)),
            ]
            body_ops = block2 + block4 + block5 + block6
            acc_back = self.join
            latch = 6
        else:
            addend = {
                "param": b, "const7": _const(7, w), "nonparam": PcodeFactInput("free", w, storage=("register", 0x5000)),
            }.get(update)
            extra = []
            if update in {"lzcount", "load"}:
                self.addend_def = _key(0x32, 21, OPC["LZCOUNT" if update == "lzcount" else "LOAD"], 2)
                extra = [
                    PcodeFactOp(self.addend_def, OPC["LZCOUNT"], "LZCOUNT", 2, w, (b,)) if update == "lzcount"
                    else PcodeFactOp(self.addend_def, OPC["LOAD"], "LOAD", 2, w, (_const(0, 8), _param(2, 8)))
                ]
                addend = _op(self.addend_def, w)
            body_ops = extra + [
                PcodeFactOp(self.inext, OPC["INT_ADD"], "INT_ADD", 2, w, (_op(self.iv, w), _const(step, w))),
                PcodeFactOp(self.anext, OPC["INT_ADD"], "INT_ADD", 2, w, (_op(self.acc, w), addend)),
            ]
            acc_back = self.anext
        header_ops[1] = replace(header_ops[1], inputs=(init_input, _op(acc_back, w)))
        if limit == "loop_carried":
            body_ops.append(PcodeFactOp(self.limit_next, OPC["INT_SUB"], "INT_SUB", 2, size, (
                _op(self.limit_def, size), _const(1, size))))
        ret_value = _op(self.acc, w)
        if return_op == "INT_ADD":
            ret_ops = [PcodeFactOp(self.ret_copy, OPC["INT_ADD"], "INT_ADD", 3, w, (ret_value, _const(1, w)))]
        else:
            ret_ops = [PcodeFactOp(self.ret_copy, OPC[return_op or "COPY"], return_op or "COPY", 3, w, (ret_value,))]
        ret_ops.append(PcodeFactOp(self.ret, OPC["RETURN"], "RETURN", 3, None, (_const(0, 8), _op(self.ret_copy, w))))
        if not body_blocks:
            body_succ = (1, 3) if extra_exit else (1,)
            if inner_cycle:
                body_succ = (1, 7)
            body_blocks = [PcodeFactBlock(
                2, _block_key(2), (1,) + ((7,) if inner_cycle else ()), body_succ,
                (1 if extra_exit else None), (3 if extra_exit else None), tuple(op.key for op in body_ops),
            )]
            if inner_cycle:
                body_blocks.append(PcodeFactBlock(7, _block_key(7), (2,), (2,), None, None, ()))
        blocks = [
            PcodeFactBlock(0, _block_key(0), (), (1,), None, None, tuple(op.key for op in init_ops)),
            PcodeFactBlock(1, _block_key(1), (0, latch), (2, 3), 2, 3, tuple(op.key for op in header_ops)),
            *body_blocks,
            PcodeFactBlock(3, _block_key(3), (1,) + ((2,) if extra_exit else ()), (), None, None,
                           tuple(op.key for op in ret_ops)),
        ]
        self.snapshot = PcodeDataflowSnapshot(
            FUNCTION, tuple(blocks), tuple(init_ops + header_ops + body_ops + ret_ops),
        )


def _summarizer():
    return StructuralRecurrenceSummarizer(None)


N = Expression.parameter("param_1", index=0, size=4)
B = Expression.parameter("param_2", index=1, size=4)
ZERO = Expression.constant(0, size=4)


def _cond(negated: bool, left=ZERO, right=N, operator="INT_SLESS") -> Condition:
    expr = Expression.binary_op(operator, left, right)
    expr.size = 1
    return Condition(expr, negated)


def _evidence(loop: _Loop, **changes) -> CountedLoopReturnBindingEvidence:
    fields = dict(
        function_identity=FUNCTION, snapshot=loop.snapshot,
        accumulator_phi_key=loop.acc, induction_phi_key=loop.iv,
    )
    fields.update(changes)
    return CountedLoopReturnBindingEvidence(**fields)


def _loop_value(*, step=1, signed=True, bias=B, residue=(1, 0, 0, 0), start=ZERO, limit=N, base=ZERO, cases=None):
    residue_cases = cases if cases is not None else (
        ResidueLoopCase(residue[0], residue[1], (residue[2], residue[3]), bias_expr=bias),
    )
    return _summarizer()._build_counted_loop_summary_value(
        base_expr=base, start_expr=start, limit_expr=limit, induction_step=step,
        residue_cases=residue_cases, result_size=4, signed_loop=signed,
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
                 kind="counted_loop_transition_evidence") -> None:
        loop = loop or _Loop()
        self.loop = loop
        evidence = evidence or _evidence(loop)
        tkey = (kind, ("accumulator_phi", loop.acc), ("header_block", _block_key(1)))
        base_info = ReturnInfo(address="0x44", value=base_value, conditions=[base_guard or _cond(True)],
                               summary_transition_evidence_key=tkey)
        loop_info = ReturnInfo(address="0x44", value=loop_value if loop_value is not None else _loop_value(),
                               conditions=[loop_guard or _cond(False)],
                               summary_transition_evidence_key=tkey)
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
    assert proposition[0] == RETURN_BINDING_PROPOSITION
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
    assert _Case(_Loop(counter_via="CAST")).run()[0] == RETURN_BINDING_PROPOSITION


def test_loop_invariant_limit_is_accepted():
    # T-inv の成立: limit が関数の入力
    assert _Case(_Loop(limit="free")).run()[0] == RETURN_BINDING_PROPOSITION


def test_limit_recomputed_from_invariant_inputs_must_equal_the_candidate_limit():
    # REVE/loop5 の `while (i < n + n)`: header の `INT_MULT(n, 2)` は不変。写しから作った limit（n * 2）と
    # 候補の limit を SMT で照合する（n のままの候補は拒否、n * 2 の候補は受理）
    doubled = Expression.binary_op("INT_MULT", N, Expression.constant(2, size=4))
    doubled.size = 4
    loop = _Loop(limit="header_mult")
    assert "C:limit" in _Case(loop).failures()
    accepted = _Case(loop, loop_value=_loop_value(limit=doubled), loop_guard=_cond(False, ZERO, doubled),
                     base_guard=_cond(True, ZERO, doubled),
                     raw_returns=[ReturnInfo(address="0x44", value=ZERO, conditions=[_cond(True, ZERO, doubled)])])
    assert accepted.run()[0] == RETURN_BINDING_PROPOSITION


def test_second_loop_exit_is_rejected():
    assert any(item.startswith("X2:") for item in _Case(_Loop(extra_exit=True)).failures())


def test_inner_cycle_is_rejected():
    assert "T6:inner_cycle" in _Case(_Loop(inner_cycle=True)).failures()


# ---------------------------------------------------------------------------
# C / E / G / Z: 候補の値と、写しから作った値の不一致
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


def test_start_value_is_read_from_the_snapshot():
    # `for (i = 3; …)`: 写しの start は 3。start 0 の候補は拒否し、start 3 の候補は受理する
    three = Expression.constant(3, size=4)
    loop = _Loop(start=3)
    assert "C:start" in _Case(loop).failures()
    accepted = _Case(loop, loop_value=_loop_value(start=three), loop_guard=_cond(False, three),
                     base_guard=_cond(True, three),
                     raw_returns=[ReturnInfo(address="0x44", value=ZERO, conditions=[_cond(True, three)])])
    assert accepted.run()[0] == RETURN_BINDING_PROPOSITION


def test_parameter_identity_comes_from_the_snapshot_not_from_the_name():
    # 写しで b が引数 2（0 始まり）なら、候補の `param_2`（番号 1）とは別の値（名前でなく番号で比べる）
    assert "U:update_mismatch" in _Case(_Loop(b_parameter=2)).failures()


def test_guard_parameter_built_by_the_tracer_is_the_snapshot_parameter():
    # 実 binary の候補の guard の引数は型・置き場所・runtime ref を持つ。写しの引数（番号だけ）と同じ値として
    # 照合する（条件と値で symbol の識別を 1 つにする: 引数は番号で識別する）
    from scripts.function_tracer_pcode.core.storage import StorageInfo

    traced = Expression.parameter(
        "param_1", index=0, data_type="int", size=4,
        storage_info=StorageInfo(is_register=True, space_name="register", space_id=548, offset=0x4000, size=4),
    )
    case = _Case(loop_guard=_cond(False, ZERO, traced), base_guard=_cond(True, ZERO, traced))
    assert case.run()[0] == RETURN_BINDING_PROPOSITION


def test_parameter_with_two_widths_is_not_compared():
    # 写しの引数 0 は 4 byte。候補の guard が引数 0 を 8 byte で使うなら、同じ値として照合しない
    wide = Expression.parameter("param_1", index=0, size=8)
    assert "C:parameter_width" in _Case(loop_guard=_cond(False, Expression.constant(0, size=8), wide)).failures()


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
# U: 1 回分の更新は写しから作る（producer の式・更新 case を信じない）
# ---------------------------------------------------------------------------


def test_update_is_read_from_the_snapshot_not_from_the_candidate():
    # 指摘 1: 写しは `acc += 7`、候補（と producer の式）は `acc += b`。写しと照合するので拒否する
    loop = _Loop(update="const7")
    assert "U:update_mismatch" in _Case(loop).failures()
    seven = Expression.constant(7, size=4)
    assert _Case(loop, loop_value=_loop_value(bias=seven)).run()[0] == RETURN_BINDING_PROPOSITION


def test_bias_term_must_match_the_snapshot_update():
    plus_one = Expression.binary_op("INT_ADD", B, Expression.constant(1, size=4))
    plus_one.size = 4
    assert "U:update_mismatch" in _Case(loop_value=_loop_value(bias=plus_one)).failures()


def test_residue_coefficient_must_match_the_snapshot_update():
    assert "U:update_mismatch" in _Case(loop_value=_loop_value(residue=(1, 0, 0, 1))).failures()


def _residue_value(even, odd):
    return _loop_value(cases=(
        ResidueLoopCase(2, 0, (0, even[0]), bias_expr=even[1]),
        ResidueLoopCase(2, 1, (0, odd[0]), bias_expr=odd[1]),
    ))


def test_body_branches_are_selected_by_their_path_conditions():
    # r1_residue の形: `if ((i & 1) == 0) c += 1; else c += b;`。body の合流の PHI は経路条件で選ぶ
    loop = _Loop(update="residue")
    assert _Case(loop, loop_value=_residue_value((1, None), (0, B))).run()[0] == RETURN_BINDING_PROPOSITION
    # 偶奇を入れ替えた候補は、どちらの case も「残った case の論理和は真」だが写しと食い違う
    assert "U:update_mismatch" in _Case(loop, loop_value=_residue_value((0, B), (1, None))).failures()


def test_incomplete_residue_partition_is_rejected():
    loop = _Loop(update="residue")
    value = _loop_value(cases=(ResidueLoopCase(2, 0, (0, 1)),))
    assert "U:residue_partition" in _Case(loop, loop_value=value).failures()


@pytest.mark.parametrize("loop,reason", [
    (_Loop(update="residue_load"), "U:update_not_lowerable:unsupported:LOAD"),   # 分岐の条件を作れない
    (_Loop(update="load"), "U:update_not_lowerable:unsupported:LOAD"),           # 更新の入力を作れない
    (_Loop(update="nonparam"), "U:update_not_lowerable:free_input_not_parameter:register"),
    (_Loop(update="lzcount"), "U:update_not_lowerable:unsupported:LZCOUNT"),     # #300 の op は式にしない
])
def test_update_that_cannot_be_lowered_is_rejected(loop, reason):
    # 経路・条件・入力のどれかを式にできなければ、落とさずに拒否する（条件の取れない分岐・delta を作れない
    # 更新・未解決の入力に当たる）
    assert reason in _Case(loop).failures()


def test_lzcount_in_the_initial_value_is_not_lowered():
    # #300: LZCOUNT は式にしないので、初期値に LZCOUNT がある summary は（tracer の式が何であれ）使わない
    assert "C:entry_value:unsupported:LZCOUNT" in _Case(_Loop(init="lzcount")).failures()


# ---------------------------------------------------------------------------
# snapshot の値を式にする（lowering）
# ---------------------------------------------------------------------------


def _lowering(snapshot, leaves=None, **kwargs) -> SnapshotLowering:
    return SnapshotLowering(snapshot, header_index=1, region=loop_region(snapshot, 1), leaves=leaves, **kwargs)


def test_lowering_refuses_loop_carried_values_without_a_placeholder():
    loop = _Loop()
    with pytest.raises(LoweringFailure, match="loop_carried_value"):
        _lowering(loop.snapshot).value(_op(loop.anext))


def test_lowering_is_bounded():
    loop = _Loop()
    with pytest.raises(LoweringFailure, match="op_bound_exceeded"):
        _lowering(loop.snapshot, max_ops=0).value(_op(loop.cmp, 1))


def test_lowering_does_not_drop_an_unbuildable_phi_input():
    # builder の式は作れない PHI の入力を飛ばす。proof の lowering は 1 つでも作れなければ止める
    loop = _Loop(update="residue")
    bad = replace(loop.snapshot.op(loop.odd), inputs=(_op(loop.acc), PcodeFactInput("free", 4, storage=("register", 0x5000))))
    snapshot = PcodeDataflowSnapshot(
        FUNCTION, loop.snapshot.blocks, tuple(bad if op.key == loop.odd else op for op in loop.snapshot.ops),
    )
    lowering = _lowering(snapshot, leaves={loop.iv: ZERO, loop.acc: ZERO})
    with pytest.raises(LoweringFailure, match="free_input_not_parameter"):
        lowering.value(_op(loop.join))


# ---------------------------------------------------------------------------
# KIND / EV / R-census: 種類・出所・census
# ---------------------------------------------------------------------------


def test_other_summary_kinds_are_rejected():
    assert _rules(_Case(kind="state_transition_loop_evidence").failures()) == {"KIND"}


def test_missing_evidence_is_rejected():
    case = _Case()
    case.proposal.return_binding_evidence = None
    assert case.failures() == ("EV:missing",)


def test_candidates_must_be_the_proposal_members():
    case = _Case()
    case.candidates = case.candidates[:1]
    assert case.failures() == ("KIND:candidates_not_bound_to_proposal",)


def test_evidence_from_another_analysis_is_rejected():
    # op の key と CFG が同じでも、写しの digest が現在の解析のものでなければ使わない
    assert "EV:pcode_source" in _Case(digest="0" * 64).failures()


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


# ---------------------------------------------------------------------------
# 指摘 2: 入力の identity（入力だけが違う解析の証拠を取り違えない）
# ---------------------------------------------------------------------------


def test_free_input_must_carry_an_identified_storage():
    with pytest.raises(ValueError, match="storage identity"):
        PcodeFactInput("free", 4)
    with pytest.raises(ValueError, match="not identified"):
        PcodeFactInput("free", 4, storage=("unique", 0x100))
    with pytest.raises(ValueError, match="non-negative index"):
        PcodeFactInput("constant", 4, constant=1, parameter_index=0)


def test_snapshots_that_differ_only_in_an_input_have_different_digests():
    # 同じ op の key・同じ CFG で、更新の入力だけが引数 1 / 引数 2 / 別の register と違う
    digests = {
        _Loop(b_parameter=1).snapshot.digest,
        _Loop(b_parameter=2).snapshot.digest,
        _Loop(update="nonparam").snapshot.digest,
    }
    assert len(digests) == 3


def test_evidence_of_an_analysis_with_other_inputs_is_not_reused():
    # 解析 A（b = 引数 1）の証拠を、op の key・CFG が同じで入力だけが違う解析 B（b = 引数 2）に渡す
    analysis_a, analysis_b = _Loop(b_parameter=1), _Loop(b_parameter=2)
    assert {op.key for op in analysis_a.snapshot.ops} == {op.key for op in analysis_b.snapshot.ops}
    assert "EV:pcode_source" in _Case(analysis_b, evidence=_evidence(analysis_a)).failures()


class _Space:
    def __init__(self, name):
        self._name = name

    def getName(self):
        return self._name


class _Address:
    def __init__(self, space, offset):
        self._space = _Space(space)
        self._offset = offset

    def getAddressSpace(self):
        return self._space

    def getOffset(self):
        return self._offset


class _Symbol:
    def __init__(self, parameter, index):
        self._parameter, self._index = parameter, index

    def isParameter(self):
        return self._parameter

    def getCategoryIndex(self):
        return self._index


class _FreeVarnode:
    def __init__(self, space="register", offset=0x4008, *, is_input=True, parameter=True, index=1):
        self._address = _Address(space, offset)
        self._is_input = is_input
        self._symbol = _Symbol(parameter, index)

    def getAddress(self):
        return self._address

    def getOffset(self):
        return self._address.getOffset()

    def isInput(self):
        return self._is_input

    def getHigh(self):
        return SimpleNamespace(getSymbol=lambda: self._symbol)


def test_producer_identifies_a_free_input_by_storage_and_parameter_number():
    item = producer._free_input(_FreeVarnode(), 4)
    assert item.storage == ("register", 0x4008) and item.parameter_index == 1
    assert producer._free_input(_FreeVarnode(is_input=False), 4).parameter_index is None
    assert producer._free_input(_FreeVarnode(space="ram", offset=-8), 8).storage == ("ram", (1 << 64) - 8)


def test_producer_refuses_a_free_input_without_a_storage_identity():
    with pytest.raises(producer._FreeInputUnidentified):
        producer._free_input(_FreeVarnode(space="unique", offset=0x80), 4)


# ---------------------------------------------------------------------------
# 指摘 3: 証拠の不変性（作成後・コピー後に中身と identity が食い違わない）
# ---------------------------------------------------------------------------


def test_evidence_holds_only_frozen_values():
    loop = _Loop()
    with pytest.raises(ValueError, match="frozen"):
        _evidence(loop, function_identity=["function_identity_v1", "bin"])
    with pytest.raises(ValueError, match="must be strings"):
        _evidence(loop, producer_failures=["x"])
    with pytest.raises(ValueError, match="tuples"):
        PcodeDataflowSnapshot(FUNCTION, list(loop.snapshot.blocks), loop.snapshot.ops)


def test_evidence_changed_after_creation_is_rejected():
    loop = _Loop()
    evidence = _evidence(loop)
    digest_before = evidence.digest
    # frozen を迂回して中身を差し替える（`acc += 7` の写し）。digest は作ったときのまま
    object.__setattr__(evidence, "snapshot", _Loop(update="const7").snapshot)
    assert evidence.digest == digest_before
    assert evidence.recomputed_digest() != evidence.digest
    assert _Case(loop, evidence=evidence).failures() == ("EV:evidence_digest_stale",)


def test_snapshot_index_changed_after_creation_does_not_change_what_the_proof_reads():
    # 写しの索引（op の key → op）を書き換えても、proof は field から作り直した写しを読む
    loop = _Loop(update="const7")
    evidence = _evidence(loop)
    forged = replace(loop.snapshot.op(loop.anext), inputs=(_op(loop.acc), _param(1)))
    loop.snapshot._ops_by_key[loop.anext] = forged
    assert loop.snapshot.op(loop.anext) is forged
    assert "U:update_mismatch" in _Case(loop, evidence=evidence).failures()


def test_copies_of_the_evidence_keep_its_identity_and_still_prove():
    from scripts.function_tracer_pcode.core.analysis import _semantic_copy

    loop = _Loop()
    evidence = _evidence(loop)
    for copied in (_semantic_copy(evidence), copy.deepcopy(evidence), replace(evidence)):
        assert copied.digest == evidence.digest == copied.recomputed_digest()
        assert _Case(loop, evidence=copied).run()[0] == RETURN_BINDING_PROPOSITION
    info = ReturnInfo(address="0x44", value=ZERO, conditions=[_cond(True)], summary_return_binding_evidence=evidence)
    assert _semantic_copy(info).summary_return_binding_evidence.digest == evidence.digest


def test_evidence_digest_is_part_of_the_proposal_digest():
    one = QuarantinedRecurrenceProposal("s" * 64, "counted_scalar_loop_summary", (), (),
                                        return_binding_evidence=_evidence(_Loop()))
    other = QuarantinedRecurrenceProposal("s" * 64, "counted_scalar_loop_summary", (), (),
                                          return_binding_evidence=_evidence(_Loop(update="const7")))
    none = QuarantinedRecurrenceProposal("s" * 64, "counted_scalar_loop_summary", (), ())
    assert len({one.digest, other.digest, none.digest}) == 3


def test_attach_moves_the_evidence_onto_the_proposal_only():
    from scripts.function_tracer_pcode.analysis.returns.summary_returns import _shared_return_binding_evidence

    loop = _Loop()
    evidence = _evidence(loop)
    with_evidence = [ReturnInfo(address="0x44", value=ZERO, conditions=[_cond(True)],
                                summary_return_binding_evidence=evidence) for _ in range(2)]
    assert _shared_return_binding_evidence(with_evidence) is evidence
    other = _evidence(_Loop(update="const7"))
    mixed = [with_evidence[0], replace(with_evidence[1], summary_return_binding_evidence=other)]
    assert _shared_return_binding_evidence(mixed) is None
    assert _shared_return_binding_evidence([replace(with_evidence[0], summary_return_binding_evidence=None)]) is None


# ---------------------------------------------------------------------------
# 指摘 4: artifact の命題は proposal・証拠・候補・規則の全部を束ねる
# ---------------------------------------------------------------------------


def _proposal_with(evidence, candidate_ids=(("c", 0), ("c", 1))):
    return SimpleNamespace(
        digest="p" * 64, return_binding_evidence=evidence,
        new_returns=tuple(SimpleNamespace(candidate_id=item) for item in candidate_ids),
    )


def _subproof(proposition):
    return RecurrenceSubproofEvidence(
        "return_binding", proposition, "recurrence_return_binding_validator_v2", dependencies=("d" * 64,),
    )


def test_return_binding_proposition_needs_every_rule():
    proposition = return_binding_proposition(_proposal_with(_evidence(_Loop())))
    assert proposition[4] == RETURN_BINDING_RULES
    with pytest.raises(ValueError, match="every rule"):
        _subproof(proposition[:4] + (("R",),))
    with pytest.raises(ValueError, match="schema"):
        _subproof(("return_binding_v1",) + proposition[1:])


def test_artifact_subproof_must_bind_this_proposal_evidence_and_candidates():
    evidence = _evidence(_Loop())
    proposal = _proposal_with(evidence)
    validate_return_binding_subproof((_subproof(return_binding_proposition(proposal)),), proposal)
    other_evidence = _proposal_with(_evidence(_Loop(update="const7")))
    other_candidates = _proposal_with(evidence, candidate_ids=(("c", 0), ("c", 9)))
    for subproof_of in (other_evidence, other_candidates):
        with pytest.raises(ValueError, match="not bound"):
            validate_return_binding_subproof((_subproof(return_binding_proposition(subproof_of)),), proposal)
    with pytest.raises(ValueError, match="exactly one"):
        validate_return_binding_subproof((), proposal)
    with pytest.raises(ValueError, match="no return binding evidence"):
        validate_return_binding_subproof((_subproof(return_binding_proposition(proposal)),), _proposal_with(None))


def test_artifact_subproof_is_rejected_when_the_evidence_changed_after_the_proof():
    evidence = _evidence(_Loop())
    proposal = _proposal_with(evidence)
    subproof = _subproof(return_binding_proposition(proposal))
    object.__setattr__(evidence, "snapshot", _Loop(update="const7").snapshot)
    with pytest.raises(ValueError, match="changed after"):
        validate_return_binding_subproof((subproof,), proposal)


# ---------------------------------------------------------------------------
# SMT の入口: P-code を読まない
# ---------------------------------------------------------------------------


def test_value_queries_never_read_the_program():
    plus = Expression.binary_op("INT_ADD", N, B)
    plus.size = 4
    swapped = Expression.binary_op("INT_ADD", B, N)
    swapped.size = 4
    assert value_queries.prove_values_equal_under(plus, swapped, ())
    assert not value_queries.prove_values_equal_under(plus, N, ())
    assert value_queries.condition_sets_equivalent([_cond(False)], [_cond(False)])
    with pytest.raises(value_queries.QueryNeedsProgram):
        value_queries._host().tracer.anything


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
