# -*- coding: utf-8 -*-
"""plan v4 PR-C（#247 の同根、不変量 I6）: 解析は stack protector の照合に見える条件を形だけで外さない。

撤去前は ``normalize_return_partition`` の最初で ``strip_stack_protector_only_conditions`` が、base の key・
定数・大きさが一致する比較（``A != B`` / ``A - B != 0``、``INDIRECT`` / ``INT_2COMP`` で包んでも）を canary の
照合と認め、return の条件から外していた。guard の object も、失敗の branch が ``__stack_chk_fail`` へ行くことも
見ないので、ふつうのコードの比較（``p[1] != (*p)[1]``）も外れ、解析は機械語と違う関数を表した。「間に書き込みが
無い」ことも今の effect summary では示せない。条件は残す（canary を仮定の premise で外すかは §0.5 Q1、対象外）。

ここで固定すること:

* (a) 反例: 照合に見える条件は、partition の正規化（本物の ``_normalize_return_partition``）を通っても、解析器の
  公開前の段と公開境界（``analyze_through_pipeline``）を通っても残る（C-M2）。撤去前は外れた。
* (b) 対照: 同じ値の return を相補な条件で併合する一般の規則は残る（形の照合なしに、意味を変えない併合）。
* (c) production（C-M1）: 本物の checker の最終判定は、計画 §4.8 の V0〜V3・``INDIRECT`` の形・対照 C1〜C5 と
  反例の形で EQ か UNKNOWN（NOT_EQ も ERROR も無い）。一部の領域だけを覆う形と条件に ``INDIRECT`` を持つ形は、
  seed の無い解析（``semantic_successor`` の view と同じ。被覆の欠けは ``return_coverage`` domain の cause）と、
  本番の解析器と同じく outcome seed のある解析（``outcome_seed=True``。outcome partition の段の cause）の両方で
  通す（§7.3 の 2・3）。撤去前、seed の無い V1_indirect と反例 user_code_partial は誤った EQ だった。
* (d) pairwise は、正確な SMT の意味が無い演算（条件の中の ``INDIRECT`` など）を比較の外へ出さず、monolithic と
  同じ ``expression_semantics_unsupported`` の UNKNOWN の結果にする（§7.3 の 2）。

左右・各 return は合成（EqBench の ground truth ではない）。
"""

from __future__ import annotations

from typing import Any, Callable, Dict, List, Tuple
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.core import AddressValueRef, Condition, Expression, ReturnInfo
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.render_smt import (
    SMT_SEMANTICS_REFUSALS,
    UnknownSmtExtensionWidthError,
    UnsupportedSmtIntrinsicError,
    UnsupportedSmtOperatorError,
)
from scripts.function_tracer_pcode.tests.unit._analyzer_pipeline_harness import analyze_through_pipeline
from scripts.function_tracer_pcode.tests.unit.test_issue185_type_hypothesis_domain import _analysis, _descriptor


# ---------------------------------------------------------------------------
# 式（合成）
# ---------------------------------------------------------------------------


def _addr_var(name: str, address_offset: int, size: int = 8) -> Expression:
    return Expression.variable(
        name, size=size,
        runtime_ref=AddressValueRef(
            address_offset=address_offset, display_hint=name, symbol_name=name,
            is_initialized=True, can_read=True, can_write=False, is_volatile=False,
        ),
    )


def _p4() -> Expression:
    return Expression.parameter("param_1", 0, data_type="int", size=4)


def _p8() -> Expression:
    return Expression.parameter("param_1", 0, data_type="long *", size=8)


def _k(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size)


def _user_reads(*, negate_address: bool = False) -> Tuple[Expression, Expression]:
    """ふつうのコード ``p[1]`` と ``(*(long **)p)[1]``（canary とは無関係）。"""

    address = Expression.binary_op("INT_ADD", _p8(), _k(8, 8))
    if negate_address:
        address = Expression.unary_op("INT_2COMP", address)
    return (
        Expression.memory(address, size=8),
        Expression.memory(Expression.binary_op("INT_ADD", Expression.memory(_p8(), size=8), _k(8, 8)), size=8),
    )


def _user_compare(operator: str = "INT_NOTEQUAL", *, negate_address: bool = False) -> Expression:
    left, right = _user_reads(negate_address=negate_address)
    return Expression.binary_op(operator, left, right)


def _ghidra_canary_sub(guard: Expression, displacement: int) -> Expression:
    """arm64 の形: ``*(INDIRECT(*guard, d)) - *(INDIRECT(guard, d)) != 0``。"""

    return Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op(
            "INT_SUB",
            Expression.memory(Expression.binary_op("INDIRECT", Expression.memory(guard, size=8), _k(displacement)), size=8),
            Expression.memory(Expression.binary_op("INDIRECT", guard, _k(displacement)), size=8),
        ),
        _k(0, 8),
    )


def _ghidra_canary_ne(guard: Expression, displacement: int) -> Expression:
    """mips64 の形: ``*(INDIRECT(*guard, d)) != *(INDIRECT(guard, d))``。"""

    return Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.memory(Expression.binary_op("INDIRECT", Expression.memory(guard, size=8), _k(displacement)), size=8),
        Expression.memory(Expression.binary_op("INDIRECT", guard, _k(displacement)), size=8),
    )


def _direct_indirect_probe() -> Expression:
    """INDIRECT を MEMORY で包まない形（撤去前の probe が別に認めていた）。"""

    guard = _k(0x111FE8, 8)
    return Expression.binary_op(
        "INT_NOTEQUAL",
        Expression.binary_op(
            "INT_SUB",
            Expression.binary_op("INDIRECT", Expression.memory(guard, size=8), _k(48)),
            Expression.memory(Expression.binary_op("INDIRECT", guard, _k(48)), size=8),
        ),
        _k(0, 8),
    )


def _int_add_canary(guard_name: str, guard_address: int, displacement: int) -> Expression:
    """計画 §4.8 の V1〜V3 の形（``INDIRECT`` を使わない、全演算を SMT で描ける canary の照合）。"""

    guard = _addr_var(guard_name, guard_address)
    slot = Expression.memory(Expression.binary_op("INT_ADD", Expression.memory(guard, size=8), _k(displacement, 8)), size=8)
    return Expression.binary_op("INT_NOTEQUAL", slot, Expression.memory(Expression.memory(guard, size=8), size=8))


def _indirect_canary(guard_name: str, guard_address: int, displacement: int) -> Expression:
    """計画 §4.8 の ``INDIRECT`` の形（実際の Ghidra の canary の読み。SMT の意味が無い）。"""

    return _ghidra_canary_ne(_addr_var(guard_name, guard_address), displacement)


_LEFT_GUARD = ("PTR___stack_chk_guard_00111fe8", 0x111FE8, 48)
_RIGHT_GUARD = ("PTR___stack_chk_guard_120013160", 0x120013160, 74)


# ---------------------------------------------------------------------------
# (a)・(b) 解析器: 条件は形だけでは外れない（C-M2）
# ---------------------------------------------------------------------------


def _analysis_with(returns: List[ReturnInfo]) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name="f", entry_point="0x1000", parameters=[], returns=returns, return_type="int",
    )


def _conditions_of(returns: List[ReturnInfo]) -> List[Tuple[Any, ...]]:
    return [tuple(condition.structural_key() for condition in info.conditions) for info in returns]


def _two_way(condition: Expression, when_true: int, when_false: int) -> List[ReturnInfo]:
    return [
        ReturnInfo(address="0x10", value=_k(when_true), conditions=[Condition(condition, False)], branch_index=0),
        ReturnInfo(address="0x20", value=_k(when_false), conditions=[Condition(condition, True)], branch_index=1),
    ]


_KEPT_SHAPES: Dict[str, Callable[[], List[ReturnInfo]]] = {
    # 計画 §4.8 の誤認（sp_probe）: ふつうのコードの比較を両極性で。撤去前は両方の条件が外れ、
    # 1 と 0 の無条件の return が重なった（順序付き ITE では関数は常に 1）。
    "user_code_notequal": lambda: _two_way(_user_compare("INT_NOTEQUAL"), 1, 0),
    "user_code_equal": lambda: _two_way(_user_compare("INT_EQUAL"), 1, 0),
    "user_code_2comp_address": lambda: _two_way(_user_compare(negate_address=True), 1, 0),
    # Ghidra の canary の形（撤去前の既存 test が「外れる」ことを固定していた形）。
    "arm64_canary_sole_return": lambda: [
        ReturnInfo(
            address="0x4000", value=_k(7),
            conditions=[Condition(_ghidra_canary_sub(_addr_var(*_LEFT_GUARD[:2]), 48), True)], branch_index=0,
        ),
    ],
    "canary_without_name_hint": lambda: [
        ReturnInfo(
            address="0x4000", value=_k(7),
            conditions=[Condition(_ghidra_canary_sub(Expression.variable("tmp_guard_base", size=8), 48), False)],
            branch_index=0,
        ),
    ],
    "canary_under_bool_negate": lambda: [
        ReturnInfo(
            address="0x4000", value=_k(7),
            conditions=[Condition(
                Expression.unary_op("BOOL_NEGATE", _ghidra_canary_sub(Expression.variable("tmp_guard_base", size=8), 48)),
                False,
            )],
            branch_index=0,
        ),
    ],
    "canary_direct_indirect_probe": lambda: [
        ReturnInfo(address="0x4000", value=_k(7), conditions=[Condition(_direct_indirect_probe(), False)], branch_index=0),
    ],
}


# 正規化は ``BOOL_NEGATE`` を条件の極性へ畳む（意味は同じ）。その形の期待は畳んだ後の条件。
_NORMALIZED_CONDITIONS: Dict[str, Callable[[], List[Tuple[Any, ...]]]] = {
    "canary_under_bool_negate": lambda: [(
        Condition(_ghidra_canary_sub(Expression.variable("tmp_guard_base", size=8), 48), True).structural_key(),
    )],
}


@pytest.mark.parametrize("shape", sorted(_KEPT_SHAPES))
def test_partition_normalization_keeps_comparisons_that_look_like_a_canary_check(shape):
    returns = _KEPT_SHAPES[shape]()
    expected = _NORMALIZED_CONDITIONS.get(shape, lambda: _conditions_of(returns))()
    analysis = _analysis_with(returns)

    ReturnAnalyzer(program=Mock(), debug=False)._normalize_return_partition(analysis)

    assert _conditions_of(analysis.returns) == expected
    assert [info.value.structural_key() for info in analysis.returns] == [info.value.structural_key() for info in returns]


def test_equal_values_under_complementary_canary_conditions_still_merge():
    """対照 (b): 同じ値の return を相補な条件で併合する一般の規則は、形の照合なしに残る（意味を変えない）。"""

    guard = _addr_var(*_RIGHT_GUARD[:2])
    condition = _ghidra_canary_ne(guard, 74)
    value = Expression.variable("guard_after_call", size=4)
    analysis = _analysis_with([
        ReturnInfo(address="0x2000", value=value, conditions=[Condition(condition, False)], branch_index=0),
        ReturnInfo(address="0x2000", value=value, conditions=[Condition(condition, True)], branch_index=1),
    ])

    ReturnAnalyzer(program=Mock(), debug=False)._normalize_return_partition(analysis)

    assert len(analysis.returns) == 1
    assert analysis.returns[0].conditions == []
    assert analysis.returns[0].value.structural_key() == value.structural_key()


def test_condition_survives_the_analyzer_stages_and_publication():
    """(a) 解析器の公開前の段（本物の ``analyze_function_by_name``）と公開境界を通しても条件は残る。"""

    condition = _user_compare()
    template = _analysis("f", [_descriptor("param_1", 8, "long *", False)], [
        ReturnInfo("0x10", _k(1), [Condition(condition, False)]),
    ])

    published = analyze_through_pipeline(template)

    assert [info.value.structural_key() for info in published.returns] == [_k(1).structural_key()]
    assert _conditions_of(published.returns) == [(Condition(condition, False).structural_key(),)]


# ---------------------------------------------------------------------------
# (c) production（C-M1）: 最終判定は EQ か UNKNOWN（NOT_EQ も ERROR も無い）
# ---------------------------------------------------------------------------


def _side(name: str, returns: List[ReturnInfo], *, pointer: bool = False) -> FunctionReturnAnalysis:
    descriptor = _descriptor("param_1", 8, "long *", False) if pointer else _descriptor("param_1", 4, "int", True)
    return _analysis(name, [descriptor], returns)


def _canary_side(name: str, guard: Tuple[str, int, int], *, kept: bool, fail_branch: bool, indirect: bool):
    """戻り値は canary が無傷なら ``param_1``。``fail_branch`` は失敗の branch が return に見える（noreturn が
    解けなかった）形で、値は 0。"""

    if not kept:
        return _side(name, [ReturnInfo("0x10", _p4(), [])])
    check = (_indirect_canary if indirect else _int_add_canary)(*guard)
    returns = [ReturnInfo("0x10", _p4(), [Condition(check, True)])]
    if fail_branch:
        returns.append(ReturnInfo("0x20", _k(0), [Condition(check, False)]))
    return _side(name, returns)


def _canary_pair(*, kept: bool, left_fail: bool, right_fail: bool, indirect: bool):
    return (
        _canary_side("left", _LEFT_GUARD, kept=kept, fail_branch=left_fail, indirect=indirect),
        _canary_side("right", _RIGHT_GUARD, kept=kept, fail_branch=right_fail, indirect=indirect),
    )


def _positive() -> Condition:
    return Condition(Expression.binary_op("INT_SLESS", _k(0), _p4()), False)


def _indirect_read() -> Expression:
    return Expression.memory(Expression.binary_op("INDIRECT", _addr_var("G", 0x1000), _k(8)), size=4)


def _full_cover(condition: Expression, value: Expression) -> List[ReturnInfo]:
    return [
        ReturnInfo("0x10", value, [Condition(condition, True)]),
        ReturnInfo("0x20", _k(0), [Condition(condition, False)]),
    ]


_PIPELINE = analyze_through_pipeline


def _seeded(template: Any) -> Any:
    return analyze_through_pipeline(template, outcome_seed=True)


_GAP = ("return_coverage_gap",)
_INCONCLUSIVE = ("return_coverage_inconclusive",)

# 一部だけを覆う形と、条件に SMT の意味の無い演算を持つ形。seed の無い解析（``semantic_successor`` の
# view と同じ）と、本番の解析器と同じく seed のある解析の両方で通す。seed の無い解析では、被覆の欠けは
# ``return_coverage`` domain の cause になる（撤去前・この domain の前は ERROR か誤った EQ だった）。
_PARTIAL_SHAPES = (
    # V1: 失敗の branch は noreturn として刈られ、return は canary の無傷の領域だけを覆う（ふつうの形）。
    ("V1_fail_branch_pruned", lambda: _canary_pair(kept=True, left_fail=False, right_fail=False, indirect=False), _GAP),
    # 実際の Ghidra の形（canary の読みに INDIRECT）。撤去前は条件が外れて誤った EQ だった。
    ("V1_indirect", lambda: _canary_pair(kept=True, left_fail=False, right_fail=False, indirect=True), _INCONCLUSIVE),
    ("V3_indirect", lambda: _canary_pair(kept=True, left_fail=True, right_fail=True, indirect=True), _INCONCLUSIVE),
    # 対照 C1・C2: canary でない条件・同じ memory の条件で一部だけ覆う（両側同じ）。
    ("C1_partial_parameter_guard", lambda: (_side("l", [ReturnInfo("0x10", _p4(), [_positive()])]),
                                           _side("r", [ReturnInfo("0x10", _p4(), [_positive()])])), _GAP),
    ("C2_partial_same_memory_guard", lambda: tuple(
        _side(name, [ReturnInfo("0x10", _p4(), [Condition(_int_add_canary("G", 0x1000, 8), True)])])
        for name in ("l", "r")
    ), _GAP),
    # 対照 C4: 全域を覆う条件の中の INDIRECT（被覆を決められない）。
    ("C4_indirect_condition", lambda: tuple(
        _side(name, _full_cover(Expression.binary_op("INT_NOTEQUAL", _indirect_read(), _p4()), _p4()))
        for name in ("l", "r")
    ), _INCONCLUSIVE),
    # 反例: 左は「比較が成り立てば 1」だけを return する（他の領域は return しない）、右は常に 1。
    # 撤去前は左の条件が外れて無条件の 1 になり、本物の checker は EQ を出した（誤った EQ）。
    ("user_code_partial_vs_constant", lambda: (
        _side("l", [ReturnInfo("0x10", _k(1), [Condition(_user_compare(), False)])], pointer=True),
        _side("r", [ReturnInfo("0x10", _k(1), [])], pointer=True),
    ), _GAP),
)

# (case id, (left, right) を作る関数, 解析の通し方, 期待する最終判定, authority で active な cause に必ずある reason)
_PRODUCTION_CASES = (
    # V0: 撤去前の除去の後の形（両側とも無条件）。対照。
    ("V0_unconditional", lambda: _canary_pair(kept=False, left_fail=False, right_fail=False, indirect=False),
     _PIPELINE, "EQUIVALENT", ()),
    # V2・V3: 失敗の branch が return に見える。V3 の canary の項は側ごとに独立なので、(左は無傷, 右は失敗)
    # の組は SAT だが、SAT は replay で曖昧として UNKNOWN（誤った NOT_EQ ではない）。
    ("V2_right_fail_branch", lambda: _canary_pair(kept=True, left_fail=False, right_fail=True, indirect=False),
     _PIPELINE, "UNKNOWN", ()),
    ("V3_both_fail_branches", lambda: _canary_pair(kept=True, left_fail=True, right_fail=True, indirect=False),
     _PIPELINE, "UNKNOWN", ()),
    # 対照 C3: 値の中の INDIRECT（両側同じ、無条件）。
    ("C3_indirect_value", lambda: tuple(_side(name, [ReturnInfo("0x10", _indirect_read(), [])]) for name in ("l", "r")),
     _PIPELINE, "UNKNOWN", ()),
    # 対照 C5: 全域を覆うふつうの条件。
    ("C5_full_cover_plain_condition", lambda: tuple(
        _side(name, _full_cover(Expression.binary_op("INT_SLESS", _k(0), _p4()), _p4())) for name in ("l", "r")
    ), _PIPELINE, "EQUIVALENT", ()),
    # 反例（§4.8 の誤認）: 左はふつうのコードの比較で 1 / 0、右は常に 1。撤去前は左の条件が両方外れた。
    ("user_code_full_cover_vs_constant", lambda: (
        _side("l", _two_way(_user_compare(), 1, 0), pointer=True),
        _side("r", [ReturnInfo("0x10", _k(1), [])], pointer=True),
    ), _PIPELINE, "UNKNOWN", ()),
    *(
        (case_id + "_seedless", make_pair, _PIPELINE, "UNKNOWN", reasons)
        for case_id, make_pair, reasons in _PARTIAL_SHAPES
    ),
    *(
        (case_id + "_seeded", make_pair, _seeded, "UNKNOWN", ())
        for case_id, make_pair, _reasons in _PARTIAL_SHAPES
    ),
)


@pytest.mark.parametrize(
    "case_id, make_pair, analyze, expected, required_reasons",
    _PRODUCTION_CASES,
    ids=[case[0] for case in _PRODUCTION_CASES],
)
def test_production_check_never_returns_not_equivalent_or_error_for_kept_conditions(
    case_id, make_pair, analyze, expected, required_reasons,
):
    from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check

    left, right = make_pair()
    result = run_production_check("pr-c-" + case_id, left, right, analyze=analyze)
    reasons = {reason.get("reason_id") for reason in result.get("unknown_reasons") or () if isinstance(reason, dict)}
    active = {row.get("reason_id") for row in result.get("c_active_base") or () if isinstance(row, dict)}

    assert result["final_outcome"] == expected, (
        result.get("final_outcome"), result.get("error_message"), result.get("failure_message"), sorted(reasons),
    )
    # authority の active な cause（legacy の診断の同じ id ではなく）が判定を UNKNOWN にしている。
    assert set(required_reasons) <= active, (sorted(active), sorted(reasons))


def test_the_seeded_analyses_carry_an_outcome_seed_and_keep_the_canary_condition():
    """(c) の前提: ``outcome_seed=True`` の解析は seed を持ち、canary の条件を残したまま比較に入る。"""

    left, _right = _canary_pair(kept=True, left_fail=False, right_fail=False, indirect=True)
    expected = _conditions_of(left.returns)

    seeded = _seeded(left)

    assert seeded.outcome_seed is not None
    assert _conditions_of(seeded.returns) == expected
    assert analyze_through_pipeline(left).outcome_seed is None


# ---------------------------------------------------------------------------
# (d) pairwise: 正確な SMT の意味が無い演算を比較の外へ出さない
# ---------------------------------------------------------------------------


_REFUSALS = (
    ("operator", lambda: UnsupportedSmtOperatorError(
        operator="INDIRECT", reason="unsupported binary operator", operand_bits=64, result_bits=64,
    ), "unsupported_smt_operator", ("unsupported_smt_operator", "INDIRECT", "unsupported binary operator", 64, 64)),
    ("intrinsic", lambda: UnsupportedSmtIntrinsicError(mnemonic="vfoo", opcode=None),
     "unsupported_intrinsic_smt_lowering", ("unsupported_smt_intrinsic", "vfoo")),
    ("extension_width", lambda: UnknownSmtExtensionWidthError(operator="INT_ZEXT", operand_bits=8),
     "unknown_smt_extension_width", ("unknown_smt_extension_width", "INT_ZEXT", 8)),
)


@pytest.mark.parametrize("kind, make_refusal, evidence, fields", _REFUSALS, ids=[row[0] for row in _REFUSALS])
def test_pairwise_turns_every_smt_semantics_refusal_into_an_unknown_result(monkeypatch, kind, make_refusal, evidence, fields):
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.proof.strategies.pairwise_services import orchestration

    refusal = make_refusal()
    assert isinstance(refusal, SMT_SEMANTICS_REFUSALS)

    def refuse(*_args, **_kwargs):
        raise refusal

    monkeypatch.setattr(orchestration, "_impl_check", refuse)
    analysis1 = _side("l", [ReturnInfo("0x10", _p4(), [])])
    analysis2 = _side("r", [ReturnInfo("0x10", _p4(), [])])
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == ["expression_semantics_unsupported"]
    reason = result.unknown_reasons[0]
    assert reason.stage == "S_PAIRWISE"
    assert tuple(reason.evidence_refs) == (evidence,)
    assert tuple(reason.object_target_key) == (
        *fields,
        tuple(analysis1.outcome_function_identity()),
        tuple(analysis2.outcome_function_identity()),
    )


def test_pairwise_condition_with_indirect_is_an_unknown_strategy_result_not_an_escaping_refusal():
    """本物の pairwise（互換の直接呼び出し）: 条件の ``INDIRECT`` は描画で拒否され、撤去前は check の外へ出た。"""

    from scripts.function_tracer_pcode.core.analysis import publish_raw_function_analysis
    from scripts.function_tracer_pcode.tests.unit._production_check_harness import (
        _production_checker,
        require_z3_cli,
    )

    require_z3_cli()
    condition = Expression.binary_op("INT_NOTEQUAL", _indirect_read(), _p4())
    analysis1, analysis2 = (
        publish_raw_function_analysis(_side(name, _full_cover(condition, _p4())).semantic_successor())
        for name in ("l", "r")
    )

    result = _production_checker().pairwise_strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert "expression_semantics_unsupported" in [reason.reason_id for reason in result.unknown_reasons]


def test_a_derived_view_coverage_verdict_does_not_block_the_raw_pair_equivalence(monkeypatch):
    """review r2 (R2-M1) / r3 (m3): 被覆の cause は pair 全体の EQ を塞ぐので、view の被覆の判定からは作らない。

    比較の途中で、seed の無い view の pair（抽象化・promotion の view と同じく ``semantic_successor`` で作る、
    一部だけを覆う return）を本物の return-coverage gate に通し、その判定（gap / inconclusive）を
    orchestration と同じく view に書き戻す。判定と印は view に付くだけで、runner の raw pair（C5）が示す
    EQ は EQ のまま。gate が判定ごとに cause を出す設計（de2bd2b6）では、ここが UNKNOWN になった。
    """

    from scripts.function_tracer_pcode.proof.obligations.snapshot import record_comparison_annotation
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check

    original = PairwiseStrategy.check
    verdicts: List[Any] = []

    def check_after_a_view_verdict(self, analysis1, analysis2, save_formula=False):
        if not verdicts:
            views = tuple(
                analysis.semantic_successor(returns=[ReturnInfo("0x10", _p4(), [_positive()])])
                for analysis in (analysis1, analysis2)
            )
            assert all(view.outcome_seed is None for view in views)
            cases = tuple(self._extract_return_cases(view) for view in views)
            reasons = self._collect_return_coverage_unsafety_reasons({}, *cases, None, None, *views)
            verdicts.append(reasons)
            for label, view in zip(("function1", "function2"), views):
                for reason in reasons:
                    if reason.startswith(label + ":return_coverage_"):
                        note = "return_case_coverage_" + reason.split(":return_coverage_", 1)[1]
                        record_comparison_annotation(view, note)
        return original(self, analysis1, analysis2, save_formula)

    monkeypatch.setattr(PairwiseStrategy, "check", check_after_a_view_verdict)
    left, right = tuple(
        _side(name, _full_cover(Expression.binary_op("INT_SLESS", _k(0), _p4()), _p4())) for name in ("l", "r")
    )

    result = run_production_check("pr-c-view-verdict", left, right, analyze=_PIPELINE)

    assert verdicts and any(":return_coverage_" in reason for reason in verdicts[0]), verdicts
    assert result["final_outcome"] == "EQUIVALENT", result.get("c_active_base")
