"""Issue #297: recurrence summary が関数の RETURN の値を表すことの証明（return binding）。

遷移の正しさ（``_validated_transition_termination``）とは別の命題である。初回は、証拠を揃えられる
counted scalar loop の summary だけを受理する。規則（すべて成り立つときだけ成立）:

- ``KIND``: 候補はすべて counted scalar loop の transition の証拠を持つ（他の種類は拒否する）。
- ``EV``: proposal に証拠があり（証拠は proposal だけが持ち、digest に入る）、producer の失敗が無く、
  関数の identity と P-code の写しの digest が **現在の解析** と一致する（別の解析の証拠を使わない）。
- ``R-census``: 写しの op の key・block の辺・RETURN の集合が、同じ HighFunction を別に数えた census
  （control profile）と一致する。census の key は full で、重複が無い。
- ``B5``: 証拠の accumulator PHI・header が、transition の key と同じ。
- ``R``: 関数の全 RETURN の値の入力が、COPY だけ（同幅）を通って accumulator PHI の出力に着く。
- ``B2``: RETURN の入力の幅 = PHI の幅 = 候補の幅 = summary の ``result_size``。
- ``X2`` / ``T6``: header の強連結成分から出る辺はちょうど 1 本で header から出る。header を除くと循環が無い。
- ``T``: header の比較は帰納変数 PHI に直接かかる strict な大小比較で、step は ±1 と向きが合う。比較の
  両辺と帰納変数は同じ幅で、limit はループ不変（外で決まるか、不変な入力の純粋な整数演算。wrap も
  非停止も起きない形だけ）。
- ``C``: 候補は base と loop の 2 つ。loop の値の step・符号・start・limit・初期値が P-code の事実と一致し、
  base の値は初期値と一致する。``E``: 閉じた式（exact lowering）がある。
- ``G``: loop の guard ⇔ ``start REL limit``、base の guard ⇔ その否定（SMT）。
- ``U``: 更新 case の抽出が何も落としておらず、各 case が「accumulator + 候補の residue の affine」と
  SMT で等しく、候補の residue がすべて使われ、case の条件の論理和が恒真。
- ``Z``: base の値が、guard の同値な raw の exact return と、その guard の下で SMT で等しい（1 つ以上）。

SMT は局所の z3 で、#298 の UB の前提を加えない。UNSAT だけを成立とし、timeout・unknown・
query を作れないときは成立しない。どれか 1 つでも成り立たなければ ``ValueError`` で拒否する
（呼び出し側は promotion を ABORTED にし、元の解析の判定を使う）。
"""

from __future__ import annotations

from typing import Any, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.analysis.recurrence import return_binding as _binding_smt
from scripts.function_tracer_pcode.analysis.recurrence.models import ResidueLoopCase
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    _runtime_expression_signature,
)
from scripts.function_tracer_pcode.core import COUNTED_LOOP_SUM_OPCODE, Condition, Expression
from scripts.function_tracer_pcode.core.expression import ExpressionType
from scripts.function_tracer_pcode.core.loop_lowering_semantics import _counted_loop_sum_semantics
from scripts.function_tracer_pcode.core.recurrence_return_binding import (
    CountedLoopReturnBindingEvidence,
    header_guard,
    induction_steps,
    input_is_loop_invariant,
    is_full_pcode_op_key,
    loop_region,
    region_exit_edges,
    region_is_acyclic_without_header,
    return_chains,
)
from scripts.function_tracer_pcode.core.runtime_refs import CountedLoopSummaryRef
from scripts.function_tracer_pcode.core.runtime_refs.pcode import PCODE_OPCODE_BY_MNEMONIC

RETURN_BINDING_PROPOSITION = "return_binding_v1"
RETURN_BINDING_RULES = (
    "KIND", "EV", "R-census", "B5", "R", "B2", "X2", "T6", "T", "C", "E", "G", "U", "Z",
)
_COUNTED_TRANSITION_TAG = "counted_loop_transition_evidence"


class ReturnBindingUnproven(ValueError):
    """return binding を示せない（``failures`` は成り立たなかった規則と理由）。"""

    def __init__(self, failures: Sequence[str]) -> None:
        self.failures = tuple(sorted(set(failures)))
        super().__init__("recurrence return binding unproven:" + ";".join(self.failures))


def validated_return_binding(analysis: Any, proposal: Any, candidates: Sequence[Any]) -> Tuple[Any, ...]:
    """成り立てば subproof の命題を返す。成り立たなければ :class:`ReturnBindingUnproven`。"""

    ids = {item.candidate_id for item in proposal.new_returns}
    members = [candidate for candidate in candidates if candidate.candidate_id in ids]
    failures = _check(analysis, proposal, members)
    if failures:
        raise ReturnBindingUnproven(failures)
    evidence = proposal.return_binding_evidence
    return (
        RETURN_BINDING_PROPOSITION,
        proposal.digest,
        evidence.digest,
        tuple(sorted(
            (member.candidate_id for member in members),
            key=lambda value: repr(value),
        )),
        RETURN_BINDING_RULES,
    )


def _check(analysis: Any, proposal: Any, members: List[Any]) -> List[str]:
    failures: List[str] = []
    if not members:
        return ["KIND:no_candidates"]
    for member in members:
        key = tuple(member.transition_evidence_key or ())
        if not key or key[0] != _COUNTED_TRANSITION_TAG:
            failures.append(f"KIND:{key[0] if key else 'none'}")
    if failures:
        return failures
    evidence = proposal.return_binding_evidence
    if not isinstance(evidence, CountedLoopReturnBindingEvidence):
        return ["EV:missing"]
    failures.extend(f"EV:producer:{item}" for item in evidence.producer_failures)
    snapshot = evidence.snapshot
    if snapshot is None:
        return failures or ["EV:no_snapshot"]
    if tuple(evidence.function_identity) != tuple(analysis.outcome_function_identity()):
        failures.append("EV:function_identity")
    if getattr(analysis, "pcode_dataflow_digest", None) != snapshot.digest:
        failures.append("EV:pcode_source")
    # 候補は proposal に束縛済み（``_bind_accepted_candidates_to_proposal``）。証拠は proposal だけが持ち、
    # その digest は proposal の digest に入るので、別の proposal の証拠は使えない。
    if failures:
        return failures

    failures.extend(_census_failures(analysis, snapshot))
    acc_key, iv_key = evidence.accumulator_phi_key, evidence.induction_phi_key
    acc_phi, iv_phi = snapshot.op(acc_key), snapshot.op(iv_key)
    if acc_phi is None or iv_phi is None or acc_phi.block_index != iv_phi.block_index:
        return failures + ["B5:loop_phis"]
    header_index = iv_phi.block_index
    fields = _transition_fields(members[0].transition_evidence_key)
    if fields.get("accumulator_phi") != acc_key:
        failures.append("B5:accumulator_phi")
    if fields.get("header_block") != snapshot.block(header_index).key:
        failures.append("B5:header_block")

    # R / B2: 関数の全 RETURN が COPY だけで accumulator PHI の出力に着く
    chains = return_chains(snapshot, acc_key)
    if not chains:
        failures.append("R:no_return")
    for chain in chains:
        if chain.status != "bound":
            failures.append(f"R:{chain.status}")
        elif chain.input_size != acc_phi.output_size:
            failures.append("B2:return_width")

    # X2 / T6
    region = loop_region(snapshot, header_index)
    exits = region_exit_edges(snapshot, region)
    if len(exits) != 1 or exits[0][0] != header_index:
        failures.append(f"X2:exits={len(exits)}")
    if not region_is_acyclic_without_header(snapshot, region, header_index):
        failures.append("T6:inner_cycle")

    # T: 停止と回数（wrap・非停止が起きない形だけ）
    guard, guard_failure = header_guard(snapshot, header_index, iv_key, region)
    steps, step_failure = induction_steps(snapshot, iv_phi, header_index, region)
    step = None
    if guard is None:
        failures.append(f"T:{guard_failure}")
    if steps is None:
        failures.append(f"T:{step_failure}")
    if guard is not None and steps is not None:
        unique = set(steps)
        expected = {"iv<L": 1, "L<iv": -1}.get(guard.continue_relation)
        if expected is None or unique != {expected}:
            failures.append(f"T:form:{guard.continue_relation}/{tuple(sorted(unique, key=repr))}")
        else:
            step = expected
        if set(guard.widths) != {iv_phi.output_size}:
            failures.append("T:width")
        compare = snapshot.op(guard.compare_key)
        if not input_is_loop_invariant(snapshot, compare.inputs[guard.limit_operand], region):
            failures.append("T:limit_not_loop_invariant")

    # C / E / G / U / Z（候補の値の意味）
    base, loop = _split_members(members)
    if base is None or loop is None:
        return failures + ["C:members"]
    loop_value = loop.return_info.value
    ref = getattr(loop_value, "runtime_ref", None)
    operands = list(getattr(loop_value, "operands", None) or ())
    if not isinstance(ref, CountedLoopSummaryRef) or len(operands) != 3:
        return failures + ["C:not_counted_sum"]
    if step is not None and int(ref.induction_step) != step:
        failures.append("C:step")
    if guard is not None and bool(ref.signed_loop) != guard.compare_mnemonic.startswith("INT_S"):
        failures.append("C:signed")
    widths = {int(ref.result_size or 0), int(loop_value.size or 0),
              int(base.return_info.value.size or 0), int(acc_phi.output_size or 0)}
    if len(widths) != 1:
        failures.append("B2:candidate_width")
    if _runtime_expression_signature(operands[1]) != evidence.start_signature:
        failures.append("C:start")
    if _runtime_expression_signature(operands[2]) != evidence.limit_signature:
        failures.append("C:limit")
    if _runtime_expression_signature(operands[0]) != evidence.initial_signature:
        failures.append("C:loop_base")
    if _runtime_expression_signature(base.return_info.value) != evidence.initial_signature:
        failures.append("C:base_value")
    if not _counted_loop_sum_semantics(loop_value, ref, None).exact_lowering_available:
        failures.append("E:not_exact")
    if guard is not None and not failures:
        failures.extend(_guard_failures(evidence, guard, base, loop))
    if not failures:
        failures.extend(_update_failures(evidence, ref))
    if not failures:
        failures.extend(_zero_trip_failures(analysis, base))
    return failures


def _census_failures(analysis: Any, snapshot: Any) -> List[str]:
    """写しを、同じ HighFunction を別に数えた control profile の census と照合する。"""

    profile = getattr(getattr(analysis, "effect_summary", None), "function_control_effect_profile", None)
    if profile is None:
        return ["R-census:no_profile"]
    out = []
    for flag in ("pcode_enumeration_complete", "cfg_edges_complete", "terminal_return_coverage_complete"):
        if not bool(getattr(profile, flag, False)):
            out.append(f"R-census:{flag}")
    census = list(getattr(profile, "region_pcode_op_keys", ()) or ())
    if any(not is_full_pcode_op_key(key) for key in census):
        out.append("R-census:fallback_key")
    if len(set(census)) != len(census):
        out.append("R-census:duplicate_key")
    if len(census) != int(getattr(profile, "pcode_op_count", -1)):
        out.append("R-census:op_count")
    if set(census) != {op.key for op in snapshot.ops}:
        out.append("R-census:op_keys")
    snapshot_edges = {
        (block.key, snapshot.block(successor).key)
        for block in snapshot.blocks
        for successor in block.successors
    }
    if snapshot_edges != set(getattr(profile, "region_cfg_edge_keys", ()) or ()):
        out.append("R-census:cfg_edges")
    returns = {key for key in census if is_full_pcode_op_key(key) and key[6] == PCODE_OPCODE_BY_MNEMONIC["RETURN"]}
    if returns != {op.key for op in snapshot.ops_with_opcode(PCODE_OPCODE_BY_MNEMONIC["RETURN"])}:
        out.append("R-census:returns")
    if len(returns) != int(getattr(profile, "return_block_count", -1)):
        out.append("R-census:return_block_count")
    return out


def _transition_fields(key: Any) -> dict:
    out = {}
    for item in tuple(key or ())[1:]:
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str):
            out.setdefault(item[0], item[1])
    return out


def _is_counted_sum(value: Any) -> bool:
    return getattr(value, "opcode", None) == COUNTED_LOOP_SUM_OPCODE or getattr(value, "name", None) == "COUNTED_LOOP_SUM"


def _split_members(members: List[Any]) -> Tuple[Optional[Any], Optional[Any]]:
    loops = [member for member in members if _is_counted_sum(member.return_info.value)]
    bases = [member for member in members if not _is_counted_sum(member.return_info.value)]
    if len(members) != 2 or len(loops) != 1 or len(bases) != 1:
        return None, None
    return bases[0], loops[0]


def _guard_failures(evidence: Any, guard: Any, base: Any, loop: Any) -> List[str]:
    operator = "INT_SLESS" if guard.compare_mnemonic.startswith("INT_S") else "INT_LESS"
    start, limit = evidence.start_expression, evidence.limit_expression
    entry = (
        Expression.binary_op(operator, start, limit) if guard.continue_relation == "iv<L"
        else Expression.binary_op(operator, limit, start)
    )
    entry.size = 1
    out = []
    if not _binding_smt.condition_sets_equivalent(list(loop.return_info.conditions or ()), [Condition(entry, False)]):
        out.append("G:loop_guard")
    if not _binding_smt.condition_sets_equivalent(list(base.return_info.conditions or ()), [Condition(entry, True)]):
        out.append("G:base_guard")
    return out


def _loop_variables(expr: Any) -> bool:
    stack = [expr]
    while stack:
        current = stack.pop()
        if current is None:
            continue
        if str(getattr(current, "name", "") or "").startswith("__loop"):
            return True
        stack.extend(list(getattr(current, "operands", None) or ()))
    return False


def _update_failures(evidence: Any, ref: Any) -> List[str]:
    """更新 case の完全性と、候補の residue / bias の field を P-code の更新 case で検査する。"""

    out = [f"U:{item}" for item in evidence.completeness.failures()]
    cases = tuple(evidence.update_cases)
    if not cases:
        out.append("U:no_cases")
    if out:
        return out
    biases = {}
    for modulus, residue, bias_expr in tuple(ref.residue_bias_terms or ()):
        if (int(modulus), int(residue)) in biases:
            return ["U:bias_term_duplicate"]
        if _loop_variables(bias_expr):
            return ["U:bias_term_not_loop_invariant"]
        biases[(int(modulus), int(residue))] = bias_expr
    residue_cases = []
    for modulus, residue, coefficient, bias in tuple(ref.residue_cases or ()):
        residue_cases.append(ResidueLoopCase(
            int(modulus), int(residue), (int(coefficient), int(bias)),
            bias_expr=biases.pop((int(modulus), int(residue)), None),
        ))
    if biases:
        return ["U:bias_term_without_residue"]
    counter_name = getattr(evidence.induction_placeholder, "name", None) or "__loop_iv"
    observed = _binding_smt.case_residues([case.conditions for case in cases], counter_name)
    declared = {(case.modulus, case.residue) for case in residue_cases}
    used = set()
    for residue in observed:
        if residue is None:
            if declared != {(1, 0)}:
                return ["U:case_residue_unknown"]
            used.add((1, 0))
        elif (int(residue[0]), int(residue[1])) not in declared:
            return [f"U:case_residue_missing:{tuple(residue)}"]
        else:
            used.add((int(residue[0]), int(residue[1])))
    if used != declared:
        out.append("U:residue_unused")
    model_cases = [
        _UpdateCaseView(tuple(case.conditions), case.update_expression,
                        _delta_view(case.update_expression, evidence.accumulator_placeholder))
        for case in cases
    ]
    if any(item.delta_expr is None for item in model_cases):
        return out + ["U:delta_unavailable"]
    if not _binding_smt.update_cases_match_residues(
        model_cases, residue_cases,
        induction_placeholder=evidence.induction_placeholder,
        accumulator_placeholder=evidence.accumulator_placeholder,
    ):
        out.append("U:update_mismatch")
    if not _binding_smt.case_guards_are_total([case.conditions for case in cases]):
        out.append("U:cases_not_total")
    return out


class _UpdateCaseView:
    """builder の ``CountedLoopUpdateCase`` と同じ属性の読み取り専用の view。"""

    __slots__ = ("conditions", "update_expr", "delta_expr")

    def __init__(self, conditions, update_expr, delta_expr) -> None:
        self.conditions = conditions
        self.update_expr = update_expr
        self.delta_expr = delta_expr


def _delta_view(update_expr: Any, accumulator_placeholder: Any) -> Optional[Any]:
    """``update - acc``（builder の検査は delta と update の両方を見るので、update から作る）。"""

    if update_expr is None or accumulator_placeholder is None:
        return None
    delta = Expression.binary_op("INT_SUB", update_expr, accumulator_placeholder)
    delta.size = int(getattr(update_expr, "size", 0) or getattr(accumulator_placeholder, "size", 0) or 4)
    return delta


def _has_unknown(expr: Any) -> bool:
    stack = [expr]
    while stack:
        current = stack.pop()
        if current is None:
            continue
        if getattr(current, "expr_type", None) == ExpressionType.UNKNOWN:
            return True
        stack.extend(list(getattr(current, "operands", None) or ()))
    return False


def _zero_trip_failures(analysis: Any, base: Any) -> List[str]:
    """base の値を、guard の同値な raw の exact return と照合する（1 つ以上、すべて等しい）。"""

    conditions = list(base.return_info.conditions or ())
    used = 0
    for raw in tuple(getattr(analysis, "returns", ()) or ()):
        if raw.value is None or _has_unknown(raw.value):
            continue
        if not _binding_smt.condition_sets_equivalent(list(raw.conditions or ()), conditions):
            continue
        if not _binding_smt.prove_values_equal_under(base.return_info.value, raw.value, conditions):
            return ["Z:refuted_or_unknown"]
        used += 1
    return [] if used else ["Z:no_equivalent_exact_raw_return"]
