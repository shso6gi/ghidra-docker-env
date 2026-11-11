"""Issue #297: recurrence summary が関数の RETURN の値を表すことの証明（return binding）。

遷移の正しさ（``_validated_transition_termination``）とは別の命題である。初回は、証拠を揃えられる
counted scalar loop の summary だけを受理する。

証拠（``CountedLoopReturnBindingEvidence``）は P-code の **事実だけ** を持つ。値の意味は、この proof が
写しから自分で作り（``proof.recurrence_pcode_semantics``）、候補の式とは SMT で照合する。producer
（builder・tracer）が作った式は信じない。規則（すべて成り立つときだけ成立）:

- ``KIND``: 候補はすべて counted scalar loop の transition の証拠を持つ（他の種類は拒否する）。
- ``EV``: proposal に証拠があり、その digest が中身から作り直した digest と一致し（作成後・コピー後に
  中身が変わっていない）、producer の失敗が無く、関数の identity と P-code の写しの digest が
  **現在の解析** と一致する（別の解析・入力だけが違う解析の証拠を使わない）。
- ``R-census``: 写しの op の key・block の辺・RETURN の集合が、同じ HighFunction を別に数えた census
  （control profile）と一致する。census の key は full で、重複が無い。
- ``B5``: 証拠の accumulator PHI・header が、transition の key と同じ。
- ``R``: 関数の全 RETURN の値の入力が、COPY だけ（同幅）を通って accumulator PHI の出力に着く。
- ``B2``: RETURN の入力の幅 = PHI の幅 = 候補の幅 = summary の ``result_size``。
- ``X2`` / ``T6``: header の強連結成分から出る辺はちょうど 1 本で header から出る。header を除くと循環が無い。
- ``T``: header の比較は帰納変数 PHI に直接かかる strict な大小比較で、step は ±1 と向きが合う。比較の
  両辺と帰納変数は同じ幅で、limit はループ不変（wrap も非停止も起きない形だけ）。
- ``C``: 候補は base と loop の 2 つ。loop の値の step・符号が P-code の事実と一致し、start・limit・
  初期値・base の値が、写しから作った start・limit・初期値と SMT で等しい。候補の式の引数は、写しの
  引数の表（Ghidra の prototype の置き場所）のその番号の値そのもの（置き場所・幅が一致）に限る
  （``C:parameter_identity``。SMT の symbol は番号で決まるので、番号だけでは同じ値と言えない）。
  ``E``: 閉じた式がある。
- ``G``: loop の guard ⇔ ``start REL limit``、base の guard ⇔ その否定（写しから作った式との SMT）。
- ``U``: 写しから作った 1 回分の更新（header の比較が続ける側のとき、body の全経路を経路条件で
  選ぶ式）が、候補の residue / bias から作る更新 ``acc + Σ[iv ≡ r (mod m)]·(c·iv + b + bias)`` と
  SMT で等しい。経路・条件・入力のどれか 1 つでも式にできなければ成り立たない（経路を落とさない）。
  bias はループ不変（PHI の分岐条件・値を含む全 node が定数・関数の引数とその純粋な演算・選択）。
- ``Z``: base の値が、guard の同値な raw の exact return と、その guard の下で SMT で等しい（1 つ以上）。

SMT は ``analysis.recurrence.value_queries``（局所の z3、#298 の UB の前提を加えない）。UNSAT だけを
成立とし、timeout・unknown・query を作れないときは成立しない。どれか 1 つでも成り立たなければ
:class:`ReturnBindingUnproven`（``ValueError``）で拒否する（呼び出し側は promotion を ABORTED にし、
元の解析の判定を使う）。
"""

from __future__ import annotations

from typing import Any, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.analysis.recurrence import value_queries
from scripts.function_tracer_pcode.core import COUNTED_LOOP_SUM_OPCODE, Condition, Expression
from scripts.function_tracer_pcode.core.expression import ExpressionType
from scripts.function_tracer_pcode.core.loop_lowering_semantics import project_loop_lowering
from scripts.function_tracer_pcode.core.recurrence_contracts import (
    RETURN_BINDING_PROPOSITION,
    RETURN_BINDING_RULES,
)
from scripts.function_tracer_pcode.core.semantic_snapshot import traverse_semantic_graph
from scripts.function_tracer_pcode.core.recurrence_return_binding import (
    CountedLoopReturnBindingEvidence,
    parameter_leaf_mismatch,
    return_binding_proposition,
    header_guard,
    induction_steps,
    input_is_loop_invariant,
    is_full_pcode_op_key,
    loop_region,
    region_exit_edges,
    region_is_acyclic_without_header,
    return_chains,
    split_phi_inputs,
)
from scripts.function_tracer_pcode.core.runtime_refs import CountedLoopSummaryRef
from scripts.function_tracer_pcode.core.runtime_refs.pcode import PCODE_OPCODE_BY_MNEMONIC
from scripts.function_tracer_pcode.proof.recurrence_pcode_semantics import LoweringFailure, SnapshotLowering

__all__ = (
    "RETURN_BINDING_PROPOSITION", "RETURN_BINDING_RULES", "ReturnBindingUnproven",
    "return_binding_proposition", "validated_return_binding",
)

_COUNTED_TRANSITION_TAG = "counted_loop_transition_evidence"
#: proof が写しの値を式にするときの、帰納変数・accumulator の placeholder（候補の式の placeholder とは
#: 別の symbol。SMT の symbol は parameter の番号で決まり、負の番号は合成の symbol）。
_INDUCTION_INDEX = -20_001
_ACCUMULATOR_INDEX = -20_002


class ReturnBindingUnproven(ValueError):
    """return binding を示せない（``failures`` は成り立たなかった規則と理由）。"""

    def __init__(self, failures: Sequence[str]) -> None:
        self.failures = tuple(sorted(set(failures)))
        super().__init__("recurrence return binding unproven:" + ";".join(self.failures))


def validated_return_binding(analysis: Any, proposal: Any, candidates: Sequence[Any]) -> Tuple[Any, ...]:
    """成り立てば subproof の命題を返す。成り立たなければ :class:`ReturnBindingUnproven`。"""

    ids = {item.candidate_id for item in proposal.new_returns}
    members = [candidate for candidate in candidates if candidate.candidate_id in ids]
    if {member.candidate_id for member in members} != ids or len(members) != len(ids):
        raise ReturnBindingUnproven(["KIND:candidates_not_bound_to_proposal"])
    failures = _check(analysis, proposal, members)
    if failures:
        raise ReturnBindingUnproven(failures)
    return return_binding_proposition(proposal)


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
    # 証拠の digest は proposal の digest に入る。中身から作り直した digest と一致しなければ、作った後に
    # 中身が変わっている（proposal の digest はもう中身を表さない）。
    if evidence.recomputed_digest() != evidence.digest:
        return ["EV:evidence_digest_stale"]
    failures.extend(f"EV:producer:{item}" for item in evidence.producer_failures)
    if evidence.snapshot is None:
        return failures or ["EV:no_snapshot"]
    # proof は field から作り直した写しだけを読む（索引・digest が field と食い違わない）
    snapshot = evidence.snapshot.rebuilt()
    if tuple(evidence.function_identity) != tuple(analysis.outcome_function_identity()):
        failures.append("EV:function_identity")
    if tuple(snapshot.function_identity) != tuple(evidence.function_identity):
        failures.append("EV:snapshot_function_identity")
    if getattr(analysis, "pcode_dataflow_digest", None) != snapshot.digest:
        failures.append("EV:pcode_source")
    if failures:
        return failures

    failures.extend(_census_failures(analysis, snapshot))
    acc_key, iv_key = evidence.accumulator_phi_key, evidence.induction_phi_key
    acc_phi, iv_phi = snapshot.op(acc_key), snapshot.op(iv_key)
    if (
        acc_phi is None or iv_phi is None or acc_phi.key == iv_phi.key
        or acc_phi.block_index != iv_phi.block_index
        or acc_phi.mnemonic != "MULTIEQUAL" or iv_phi.mnemonic != "MULTIEQUAL"
    ):
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
    if failures:
        return failures

    # C / E / G / U / Z（候補の値の意味。写しから作った式と照合する）
    base, loop = _split_members(members)
    if base is None or loop is None:
        return ["C:members"]
    loop_value = loop.return_info.value
    ref = getattr(loop_value, "runtime_ref", None)
    operands = list(getattr(loop_value, "operands", None) or ())
    if not isinstance(ref, CountedLoopSummaryRef) or len(operands) != 3:
        return ["C:not_counted_sum"]
    if int(ref.induction_step) != step:
        failures.append("C:step")
    if bool(ref.signed_loop) != guard.compare_mnemonic.startswith("INT_S"):
        failures.append("C:signed")
    widths = {int(ref.result_size or 0), int(loop_value.size or 0),
              int(base.return_info.value.size or 0), int(acc_phi.output_size or 0)}
    if len(widths) != 1:
        failures.append("B2:candidate_width")
    if not project_loop_lowering(loop_value, ref, identity=None).exact_lowering_available:
        failures.append("E:not_exact")
    if failures:
        return failures
    facts, fact_failure = _loop_facts(snapshot, header_index, region, iv_phi, acc_phi, guard)
    if fact_failure is not None:
        return [fact_failure]
    # 引数は番号で同じ symbol になる。候補の引数が、写しの引数の表のその番号の値そのもの（置き場所・幅が
    # 一致する）でなければ照合しない（写しの側は表と照合した入力だけを引数にする）
    candidate_roots = (
        loop_value, base.return_info.value,
        *(item.expression for member in (base, loop) for item in member.return_info.conditions or ()),
        *(term[2] for term in tuple(ref.residue_bias_terms or ())),
    )
    identity = _parameter_identity_failure(snapshot, candidate_roots)
    if identity is not None:
        return [f"C:parameter_identity:{identity}"]
    for rule, candidate_value, fact in (
        ("C:start", operands[1], facts.start), ("C:limit", operands[2], facts.limit),
        ("C:loop_base", operands[0], facts.initial), ("C:base_value", base.return_info.value, facts.initial),
    ):
        if not value_queries.prove_values_equal_under(candidate_value, fact, ()):
            failures.append(rule)
    if failures:
        return failures
    failures.extend(_guard_failures(facts, guard, base, loop))
    if not failures:
        failures.extend(_update_failures(facts, ref))
    if not failures:
        failures.extend(_zero_trip_failures(analysis, base, snapshot))
    return failures


class _LoopFacts:
    """写しから作ったループの値（start・limit・初期値・1 回分の更新・続ける条件）。"""

    __slots__ = ("start", "limit", "initial", "next_value", "continue_condition", "induction", "accumulator")

    def __init__(self, **values: Any) -> None:
        for name, value in values.items():
            setattr(self, name, value)


def _loop_facts(snapshot, header_index, region, iv_phi, acc_phi, guard) -> Tuple[Optional[_LoopFacts], Optional[str]]:
    induction = Expression.parameter("__return_binding_iv", index=_INDUCTION_INDEX, size=int(iv_phi.output_size))
    accumulator = Expression.parameter(
        "__return_binding_acc", index=_ACCUMULATOR_INDEX, size=int(acc_phi.output_size),
    )
    iv_split = split_phi_inputs(snapshot, iv_phi, header_index, region)
    acc_split = split_phi_inputs(snapshot, acc_phi, header_index, region)
    if iv_split is None or acc_split is None or len(iv_split[0]) != 1 or len(acc_split[0]) != 1:
        return None, "C:entry_edge"
    if not acc_split[1]:
        return None, "U:no_backedge"
    # ループに入る前の値（帰納変数・accumulator に着いたら作れない: 入る前の値ではない）
    entry = SnapshotLowering(snapshot, header_index=header_index, region=region)
    # 1 回分の反復の値（header の PHI を placeholder にする）
    iteration = SnapshotLowering(
        snapshot, header_index=header_index, region=region,
        leaves={iv_phi.key: induction, acc_phi.key: accumulator},
    )
    cbranch = snapshot.op(guard.cbranch_key)
    block = snapshot.block(header_index)
    try:
        start = entry.value(iv_phi.inputs[iv_split[0][0]])
        initial = entry.value(acc_phi.inputs[acc_split[0][0]])
        limit = entry.value(snapshot.op(guard.compare_key).inputs[guard.limit_operand])
    except LoweringFailure as exc:
        return None, f"C:entry_value:{exc.reason}"
    try:
        condition = iteration.branch_test(cbranch.inputs[1])
        continue_condition = Condition(condition, block.true_successor not in region)
        backedges = [
            (iteration.edge_condition(block.predecessors[index], header_index), iteration.value(acc_phi.inputs[index]))
            for index in acc_split[1]
        ]
        next_value = iteration.select(backedges, int(acc_phi.output_size))
    except LoweringFailure as exc:
        return None, f"U:update_not_lowerable:{exc.reason}"
    return _LoopFacts(
        start=start, limit=limit, initial=initial, next_value=next_value,
        continue_condition=continue_condition, induction=induction, accumulator=accumulator,
    ), None


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


def _guard_failures(facts: _LoopFacts, guard: Any, base: Any, loop: Any) -> List[str]:
    operator = "INT_SLESS" if guard.compare_mnemonic.startswith("INT_S") else "INT_LESS"
    entry = (
        Expression.binary_op(operator, facts.start, facts.limit) if guard.continue_relation == "iv<L"
        else Expression.binary_op(operator, facts.limit, facts.start)
    )
    entry.size = 1
    out = []
    if not value_queries.condition_sets_equivalent(list(loop.return_info.conditions or ()), [Condition(entry, False)]):
        out.append("G:loop_guard")
    if not value_queries.condition_sets_equivalent(list(base.return_info.conditions or ()), [Condition(entry, True)]):
        out.append("G:base_guard")
    return out


def _nodes(*roots: Any) -> List[Any]:
    """式の DAG の全 node（PHI の分岐条件・値を含む。辺の分解は ``core.semantic_snapshot`` が唯一の owner）。"""

    out: List[Any] = []
    seen = set()
    for root in roots:
        for node in traverse_semantic_graph(root).entry_order:
            if id(node) not in seen:
                seen.add(id(node))
                out.append(node)
    return out


def _parameter_identity_failure(snapshot: Any, roots: Sequence[Any]) -> Optional[str]:
    for node in _nodes(*roots):
        if getattr(node, "expr_type", None) == ExpressionType.PARAMETER:
            mismatch = parameter_leaf_mismatch(snapshot, node)
            if mismatch is not None:
                return mismatch
    return None


#: ループ不変と言える式の node の種類（定数・関数の引数と、その純粋な演算・選択）。memory の読み取り・
#: call・変数・unknown は、ループの中で値が変わり得るので含めない。
_LOOP_INVARIANT_KINDS = frozenset({
    ExpressionType.CONSTANT, ExpressionType.PARAMETER, ExpressionType.BINARY_OP,
    ExpressionType.UNARY_OP, ExpressionType.PHI,
})


def _is_loop_invariant(expr: Any) -> bool:
    """bias の式がループ不変であること（PHI の分岐条件・値を含む全 node を辿る）。

    引数は番号 0 以上（関数の引数）だけを認める。負の番号は placeholder（帰納変数・accumulator）である。
    """

    for node in _nodes(expr):
        kind = getattr(node, "expr_type", None)
        if kind not in _LOOP_INVARIANT_KINDS:
            return False
        if kind == ExpressionType.PARAMETER and not (isinstance(node.value, int) and node.value >= 0):
            return False
    return True


def _update_failures(facts: _LoopFacts, ref: Any) -> List[str]:
    """写しの 1 回分の更新が、候補の residue / bias から作る更新と等しいこと（続ける条件の下で）。"""

    model, failure = _candidate_update(facts, ref)
    if failure is not None:
        return [failure]
    if not value_queries.prove_values_equal_under(facts.next_value, model, [facts.continue_condition]):
        return ["U:update_mismatch"]
    return []


def _candidate_update(facts: _LoopFacts, ref: Any) -> Tuple[Optional[Expression], Optional[str]]:
    """``acc + Σ[iv & (m-1) == r]·(c·iv + b + bias)``（候補の summary が仮定する 1 回分の更新）。"""

    size = int(facts.accumulator.size)
    biases = {}
    for modulus, residue, bias_expr in tuple(ref.residue_bias_terms or ()):
        key = (int(modulus), int(residue))
        if key in biases:
            return None, "U:bias_term_duplicate"
        if bias_expr is None or not _is_loop_invariant(bias_expr) or int(getattr(bias_expr, "size", 0) or 0) != size:
            return None, "U:bias_term_shape"
        biases[key] = bias_expr
    cases = []
    for modulus, residue, coefficient, bias in tuple(ref.residue_cases or ()):
        cases.append((int(modulus), int(residue), int(coefficient), int(bias), biases.pop((int(modulus), int(residue)), None)))
    if biases:
        return None, "U:bias_term_without_residue"
    moduli = {case[0] for case in cases}
    if len(moduli) != 1:
        return None, "U:residue_moduli"
    modulus = moduli.pop()
    if modulus <= 0 or (modulus & (modulus - 1)) != 0:
        return None, "U:residue_modulus"
    if sorted(case[1] for case in cases) != list(range(modulus)):
        return None, "U:residue_partition"
    if any(case[2] != 0 for case in cases) and int(facts.induction.size) != size:
        return None, "U:counter_width"
    branches = []
    for _modulus, residue, coefficient, bias, bias_expr in sorted(cases, key=lambda item: item[1]):
        delta = _affine(facts.induction, coefficient, bias, bias_expr, size)
        value = _binary("INT_ADD", facts.accumulator, delta, size)
        if modulus == 1:
            branches.append((None, value))
            continue
        mask = _binary("INT_AND", facts.induction, Expression.constant(modulus - 1, size=int(facts.induction.size)),
                       int(facts.induction.size))
        test = _binary("INT_EQUAL", mask, Expression.constant(residue, size=int(facts.induction.size)), 1)
        branches.append((Condition(test, False), value))
    if len(branches) == 1:
        return branches[0][1], None
    phi = Expression.phi(branches)
    phi.size = size
    return phi, None


def _affine(counter: Expression, coefficient: int, bias: int, bias_expr: Optional[Expression], size: int) -> Expression:
    mask = (1 << (8 * size)) - 1
    total: Optional[Expression] = None
    if coefficient:
        total = _binary("INT_MULT", counter, Expression.constant(coefficient & mask, size=size), size)
    if bias:
        constant = Expression.constant(bias & mask, size=size)
        total = constant if total is None else _binary("INT_ADD", total, constant, size)
    if bias_expr is not None:
        total = bias_expr if total is None else _binary("INT_ADD", total, bias_expr, size)
    return total if total is not None else Expression.constant(0, size=size)


def _binary(operator: str, left: Expression, right: Expression, size: int) -> Expression:
    expr = Expression.binary_op(operator, left, right)
    expr.size = size
    return expr


def _has_unknown(expr: Any) -> bool:
    return any(getattr(node, "expr_type", None) == ExpressionType.UNKNOWN for node in _nodes(expr))


def _zero_trip_failures(analysis: Any, base: Any, snapshot: Any) -> List[str]:
    """base の値を、guard の同値な raw の exact return と照合する（1 つ以上、すべて等しい）。

    raw の return の引数も、写しの引数の表と置き場所が一致するものだけを照合に使う。
    """

    conditions = list(base.return_info.conditions or ())
    used = 0
    for raw in tuple(getattr(analysis, "returns", ()) or ()):
        if raw.value is None or _has_unknown(raw.value):
            continue
        raw_roots = (raw.value, *(item.expression for item in raw.conditions or () if item is not None))
        if _parameter_identity_failure(snapshot, raw_roots) is not None:
            continue
        if not value_queries.condition_sets_equivalent(list(raw.conditions or ()), conditions):
            continue
        if not value_queries.prove_values_equal_under(base.return_info.value, raw.value, conditions):
            return ["Z:refuted_or_unknown"]
        used += 1
    return [] if used else ["Z:no_equivalent_exact_raw_return"]
