"""Issue #297: counted scalar loop の summary が RETURN の値を表すことの証拠を作る（producer）。

ここが P-code を読む唯一の場所である。

- :func:`_impl__capture_pcode_dataflow_snapshot` は関数の P-code の事実を 1 回だけ読み、
  ``PcodeDataflowSnapshot`` にする。走査は解析の census（control profile の block 数・op 数）を上限にし、
  上限を超えたら写しを作らない（記録の足りない iterator で回り続けない）。
- :func:`_impl__counted_loop_return_binding_evidence` は、写しと、builder が 1 回の抽出で得た
  更新 case・完全性の記録を束ねる。start / limit / 初期値の式は、写しから選んだ varnode から作る。

どの規則が成り立つかは判定しない（``proof.recurrence_return_binding`` が判定する）。
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.recurrence_return_binding import (
    CountedLoopReturnBindingEvidence,
    CountedUpdateCase,
    PcodeDataflowSnapshot,
    PcodeFactBlock,
    PcodeFactInput,
    PcodeFactOp,
    UpdateCaseCompleteness,
    header_guard,
    loop_region,
    split_phi_inputs,
)
from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeBlockRef, PcodeOpRef
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    _runtime_conditions_signature,
    _runtime_expression_signature,
)

#: Ghidra / 記録 object の読み取りで起こり得る失敗（broad except は使わない）。
_READ_FAILURES = (AttributeError, TypeError, ValueError, IndexError, RuntimeError)


class _SnapshotBoundExceeded(Exception):
    """走査が census の上限を超えた（記録の足りない iterator・壊れた CFG）。"""


def _bounded(iterator_factory, budget: List[int]):
    """Java の ``hasNext``/``next`` の iterator（または Python の iterable）を、共有の残り予算
    ``budget[0]`` の範囲で回す。予算を超えたら :class:`_SnapshotBoundExceeded`。"""

    iterator = iterator_factory()
    if iterator is None:
        return
    if hasattr(iterator, "hasNext"):
        while iterator.hasNext():
            if budget[0] <= 0:
                raise _SnapshotBoundExceeded()
            budget[0] -= 1
            yield iterator.next()
        return
    for item in iterator:
        if budget[0] <= 0:
            raise _SnapshotBoundExceeded()
        budget[0] -= 1
        yield item


def _java_iterator(collection):
    """Java の collection は ``iterator()``、Python の値はそのまま返す（上限は呼び出し側の ``_bounded``）。"""

    factory = getattr(collection, "iterator", None)
    return factory() if callable(factory) else collection


def _seq_identity(op) -> Optional[Tuple[Any, ...]]:
    seq = op.getSeqnum()
    if seq is None:
        return None
    target = seq.getTarget()
    return (
        str(target.getAddressSpace().getName()), int(target.getOffset()),
        int(seq.getTime()), int(seq.getOrder()),
    )


def _impl__capture_pcode_dataflow_snapshot(
    self, high_function, analysis,
) -> Tuple[Optional[PcodeDataflowSnapshot], Dict[Tuple[Any, ...], Any], Optional[str]]:
    """HighFunction の P-code の事実を 1 回で読む。``(写し, key → live op, 失敗の理由)`` を返す。

    上限は ``FunctionControlEffectProfile`` の ``block_count`` / ``pcode_op_count``（同じ HighFunction を
    別に数えた census）。上限を超える・識別が full でない・形が壊れているときは写しを作らない。
    """

    profile = getattr(getattr(analysis, "effect_summary", None), "function_control_effect_profile", None)
    block_budget = [int(getattr(profile, "block_count", 0) or 0)]
    op_budget = [int(getattr(profile, "pcode_op_count", 0) or 0)]
    if profile is None or block_budget[0] <= 0 or op_budget[0] <= 0:
        return None, {}, "census_unavailable"
    try:
        function_identity = analysis.outcome_function_identity()
    except _READ_FAILURES:
        return None, {}, "function_identity_unavailable"
    tracer = self.tracer
    identity = dict(
        binary_id=getattr(tracer, "_function_binary_id", None),
        program_uid=getattr(tracer, "_function_program_id", None),
        function_entry_space=getattr(tracer, "_function_entry_space", None),
        function_entry_offset=getattr(tracer, "_function_entry_offset", None),
    )
    try:
        raw_blocks = list(_bounded(lambda: _java_iterator(high_function.getBasicBlocks()), block_budget))
        live_ops: Dict[Tuple[Any, ...], Any] = {}
        key_by_seq: Dict[Tuple[Any, ...], Tuple[Any, ...]] = {}
        ops_by_block: List[Tuple[Any, List[Tuple[Tuple[Any, ...], Any]]]] = []
        for block in raw_blocks:
            listed = []
            for ordinal, op in enumerate(_bounded(block.getIterator, op_budget)):
                ref = PcodeOpRef.from_pcode_op(op, local_op_ordinal=ordinal, **identity)
                if ref is None or not ref._has_full_identity_context():
                    return None, {}, "op_identity_incomplete"
                key = ref.stable_key()
                seq = _seq_identity(op)
                if key in live_ops or seq is None or seq in key_by_seq:
                    return None, {}, "op_identity_duplicate"
                live_ops[key] = op
                key_by_seq[seq] = key
                listed.append((key, op))
            ops_by_block.append((block, listed))
        fact_ops = []
        fact_blocks = []
        for block, listed in ops_by_block:
            index = int(block.getIndex())
            for key, op in listed:
                inputs = []
                for position in range(int(op.getNumInputs())):
                    varnode = op.getInput(position)
                    size = int(varnode.getSize())
                    if bool(varnode.isConstant()):
                        inputs.append(PcodeFactInput("constant", size, constant=int(varnode.getOffset())))
                        continue
                    definition = varnode.getDef()
                    if definition is None:
                        inputs.append(PcodeFactInput("free", size))
                        continue
                    producer = key_by_seq.get(_seq_identity(definition))
                    if producer is None:
                        return None, {}, "def_outside_function"
                    inputs.append(PcodeFactInput("op", size, producer_key=producer))
                output = op.getOutput()
                fact_ops.append(PcodeFactOp(
                    key=key,
                    opcode=int(op.getOpcode()),
                    mnemonic=str(op.getMnemonic()),
                    block_index=index,
                    output_size=None if output is None else int(output.getSize()),
                    inputs=tuple(inputs),
                ))
            block_ref = PcodeBlockRef(
                block_index=index,
                start_address_offset=int(block.getStart().getOffset()),
                binary_id=identity["binary_id"] or identity["program_uid"],
                function_entry_space=identity["function_entry_space"],
                function_entry_offset=identity["function_entry_offset"],
            )
            successors = tuple(int(block.getOut(i).getIndex()) for i in range(int(block.getOutSize())))
            true_out = block.getTrueOut() if len(successors) == 2 else None
            false_out = block.getFalseOut() if len(successors) == 2 else None
            fact_blocks.append(PcodeFactBlock(
                index=index,
                key=block_ref.stable_key(),
                predecessors=tuple(int(block.getIn(i).getIndex()) for i in range(int(block.getInSize()))),
                successors=successors,
                true_successor=None if true_out is None else int(true_out.getIndex()),
                false_successor=None if false_out is None else int(false_out.getIndex()),
                op_keys=tuple(key for key, _op in listed),
            ))
        snapshot = PcodeDataflowSnapshot(
            function_identity=tuple(function_identity),
            blocks=tuple(fact_blocks),
            ops=tuple(fact_ops),
        )
    except _SnapshotBoundExceeded:
        return None, {}, "scan_bound_exceeded"
    except _READ_FAILURES as exc:
        return None, {}, f"snapshot_read_failed:{type(exc).__name__}"
    return snapshot, live_ops, None


def _impl__counted_loop_return_binding_evidence(
    self,
    *,
    high_function,
    analysis,
    induction,
    accumulator,
    update_cases: Sequence[Any],
    completeness: UpdateCaseCompleteness,
) -> CountedLoopReturnBindingEvidence:
    """counted scalar loop の summary 1 つの証拠を作る。揃わないものは ``producer_failures`` に書く。"""

    failures: List[str] = []
    try:
        function_identity = tuple(analysis.outcome_function_identity())
    except _READ_FAILURES:
        function_identity = ("function_identity_unavailable",)
        failures.append("function_identity_unavailable")
    snapshot, live_ops, failure = self._capture_pcode_dataflow_snapshot(high_function, analysis)
    if failure:
        failures.append(failure)
    acc_key = iv_key = None
    start_expr = limit_expr = init_expr = None
    if snapshot is not None:
        acc_key = _live_key(live_ops, accumulator.phi_op)
        iv_key = _live_key(live_ops, induction.phi_op)
        header_index = int(induction.phi_op.getParent().getIndex())
        region = loop_region(snapshot, header_index)
        if acc_key is None or iv_key is None:
            failures.append("loop_phi_not_in_snapshot")
        else:
            iv_split = split_phi_inputs(snapshot, snapshot.op(iv_key), header_index, region)
            acc_split = split_phi_inputs(snapshot, snapshot.op(acc_key), header_index, region)
            if iv_split is None or len(iv_split[0]) != 1:
                failures.append("induction_entry_edge")
            else:
                start_expr = self._build_pcode_expression(
                    induction.phi_op.getInput(iv_split[0][0]),
                    placeholders={induction.phi_output: induction.placeholder},
                )
            if acc_split is None or len(acc_split[0]) != 1:
                failures.append("accumulator_entry_edge")
            else:
                entry_varnode = accumulator.phi_op.getInput(acc_split[0][0])
                init_expr = self._trace_varnode_expression(entry_varnode)
                if init_expr is None or self._expression_is_unresolved(init_expr):
                    init_expr = self._build_pcode_expression(entry_varnode, placeholders={})
            guard, guard_failure = header_guard(snapshot, header_index, iv_key, region)
            if guard is None:
                failures.append(f"header_guard:{guard_failure}")
            else:
                compare = live_ops[guard.compare_key]
                limit_expr = self._build_pcode_expression(
                    compare.getInput(guard.limit_operand),
                    placeholders={induction.phi_output: induction.placeholder},
                )
        for name, expr in (("start", start_expr), ("limit", limit_expr), ("initial", init_expr)):
            if expr is None or self._expression_is_unresolved(expr):
                if not any(item.startswith(name) or item.endswith("entry_edge") for item in failures):
                    failures.append(f"{name}_unresolved")
        if analysis.pcode_dataflow_digest is None:
            analysis.pcode_dataflow_digest = snapshot.digest
        elif analysis.pcode_dataflow_digest != snapshot.digest:
            failures.append("pcode_dataflow_digest_conflict")
    cases = tuple(
        CountedUpdateCase(
            conditions=tuple(case.conditions or ()),
            update_expression=case.update_expr,
            conditions_signature=_runtime_conditions_signature(list(case.conditions or ())),
            update_signature=_runtime_expression_signature(case.update_expr),
        )
        for case in update_cases or ()
    )
    return CountedLoopReturnBindingEvidence(
        function_identity=function_identity,
        snapshot=snapshot,
        accumulator_phi_key=acc_key,
        induction_phi_key=iv_key,
        start_expression=start_expr,
        limit_expression=limit_expr,
        initial_expression=init_expr,
        induction_placeholder=induction.placeholder,
        accumulator_placeholder=accumulator.placeholder,
        start_signature=_runtime_expression_signature(start_expr) if start_expr is not None else (),
        limit_signature=_runtime_expression_signature(limit_expr) if limit_expr is not None else (),
        initial_signature=_runtime_expression_signature(init_expr) if init_expr is not None else (),
        update_cases=cases,
        completeness=completeness,
        producer_failures=tuple(failures),
    )


def _live_key(live_ops: Dict[Tuple[Any, ...], Any], op) -> Optional[Tuple[Any, ...]]:
    """live op の key（SeqNum で照合する。Python の object の同一性は使わない）。"""

    if op is None:
        return None
    target = _seq_identity(op)
    for key, candidate in live_ops.items():
        if _seq_identity(candidate) == target:
            return key
    return None


# ---------------------------------------------------------------------------
# proof が使う SMT の入口（局所の z3。UB の前提を加えない。UNSAT だけを成立とし、
# timeout・unknown・query を作れないときは成立しない）
# ---------------------------------------------------------------------------


def _smt_summarizer():
    from scripts.function_tracer_pcode.analysis.recurrence.summarizer import StructuralRecurrenceSummarizer

    # P-code を読まない式の検査だけに使う（tracer を持たない）
    return StructuralRecurrenceSummarizer(None)


def prove_values_equal_under(left, right, conditions: Sequence[Any]) -> bool:
    """``conditions`` の下で ``left == right`` が恒真であること。"""

    summarizer = _smt_summarizer()
    parameters = summarizer._collect_summary_parameter_specs(
        left, right, *(item.expression for item in conditions or () if item is not None),
    )
    return bool(summarizer._prove_expression_equivalence_under_conditions(
        left, right, list(conditions or ()), parameters,
    ))


def condition_sets_equivalent(left: Sequence[Any], right: Sequence[Any]) -> bool:
    return bool(_smt_summarizer()._condition_sets_equivalent(list(left or ()), list(right or ())))


def case_guards_are_total(case_conditions: Sequence[Sequence[Any]]) -> bool:
    """case の条件（連言）の論理和が恒真であること。loop の placeholder を含んでよい
    （条件の oracle は placeholder を描けないので、式の同値の query で示す）。"""

    from scripts.function_tracer_pcode.core import Condition, Expression

    disjunction = None
    for conditions in case_conditions:
        conditions = list(conditions or ())
        if not conditions:
            return True
        conjunction = Condition.combine_and(conditions)
        if conjunction is None:
            return False
        expr = conjunction.expression
        if bool(getattr(conjunction, "negated", False)):
            expr = Expression.unary_op("BOOL_NEGATE", expr)
            expr.size = 1
        if disjunction is None:
            disjunction = expr
        else:
            disjunction = Expression.binary_op("BOOL_OR", disjunction, expr)
            disjunction.size = 1
    if disjunction is None:
        return False
    return prove_values_equal_under(disjunction, Expression.constant(1, size=1), ())


def case_residues(conditions_by_case: Sequence[Sequence[Any]], counter_name: str) -> Tuple[Optional[Tuple[int, int]], ...]:
    """各 case の条件から読める counter の剰余 ``(modulus, residue)``（読めなければ None）。"""

    summarizer = _smt_summarizer()
    return tuple(
        summarizer._extract_exact_residue_case(list(conditions or ()), counter_name)
        for conditions in conditions_by_case
    )


def update_cases_match_residues(
    cases: Sequence[Any], residue_cases: Sequence[Any], *, induction_placeholder, accumulator_placeholder,
) -> bool:
    """builder と同じ検査（``_validate_update_cases_against_residue_cases``）を、渡した residue で行う。"""

    return bool(_smt_summarizer()._validate_update_cases_against_residue_cases(
        cases=cases,
        residue_cases=residue_cases,
        induction_placeholder=induction_placeholder,
        accumulator_placeholder=accumulator_placeholder,
    ))
