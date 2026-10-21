# -*- coding: utf-8 -*-
"""対応の証拠の無い自由入力に依存する SAT を NOT_EQ にしない（U-21）。

引数ではない入力（スタック上の ``in_stack_*``、parameter ではない register の ``unaff_*``）は
builder が左右別の自由記号（extra variable）として宣言する。parameter と違って、その記号の左右の
対応を示す relation は無いので、SAT の model はそれに左右で別々の値を与えてよい。両側が同じ入力を
同じように返す等価な関数でも、model（``_1 = 0``、``_2 = 1``）が見つかり、replay も model の値を
固定して評価し直すだけなので通ってしまい、両 strategy で最終 NOT_EQ になっていた。

守る契約（``proof_gates/sat_safety.py`` の ``_unpaired_input_unsafety_reasons``）:

* SAT を decisive とするのは、query が宣言した自由入力記号がすべて、query の
  ``InputCorrespondenceSet`` の十分な relation が覆う記号（``covered_input_names``）のときだけ。
* 覆われない記号があれば ``pair:unpaired_input:<side>:<name>`` の ref を出す。型は解析の不安全で、
  登録済みの ``counterexample_analysis_safety_unproven`` に写り、replay では解消しない。
* UNSAT（EQ）は変えない。記号の名前や由来で判定しない。
"""

from __future__ import annotations

from contextlib import contextmanager
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.core import Expression, ReturnInfo
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    LEFT,
    RIGHT,
    InputCorrespondence,
    InputCorrespondenceSet,
    InputRelationKind,
    SideParameter,
    build_tie_only_correspondence_set,
)
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.proof.sat_safety_resolution import (
    COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN,
    SatSafetyResolution,
    classify_sat_safety_blocker,
    replay_may_resolve_sat_safety_reason,
)
from scripts.function_tracer_pcode.proof.strategies.base import CheckStrategy
from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check
from scripts.function_tracer_pcode.tests.unit.test_issue185_type_hypothesis_domain import _analysis, _descriptor

_REF = "pair:unpaired_input:"
#: parameter の storage を与える（storage が不明だと別の理由 ``hidden_input`` で偶然止まる）。
_PARAM_STORAGE = {
    "is_register": True, "space_name": "register", "offset": 0x38, "size": 4, "size_bits": 32,
    "register_name": "EDI", "base_register_name": "RDI", "base_register_offset": 0x38,
    "base_register_size": 8, "base_register_size_bits": 64, "bit_offset_in_base": 0,
}


def _param():
    return Expression.parameter("param_1", 0, data_type="int", size=4)


def _stack_input(name="in_stack_00000008", *, storage="stack"):
    if storage == "stack":
        info = StorageInfo(is_register=False, space_name="stack", offset=8, size=4, size_bits=32)
        return Expression.variable(name, data_type="int", size=4, storage_info=info)
    if storage is None:
        return Expression.variable(name, data_type="int", size=4, storage_info=None)
    info = StorageInfo(
        is_register=True, space_name="register", offset=0x98, size=8, size_bits=64,
        register_name="RBX", base_register_name="RBX", base_register_offset=0x18,
        base_register_size=8, base_register_size_bits=64,
    )
    value = Expression.binary_op(
        "SUBPIECE", Expression.variable(name, data_type="int", size=8, storage_info=info), Expression.constant(0, 4),
    )
    value.size = 4
    return value


def _side(name, value):
    return _analysis(
        name, [_descriptor("param_1", 4, "int", True, storage=dict(_PARAM_STORAGE))], [ReturnInfo("0x10", value, [])],
    )


#: 両側が同じ引数でない入力を同じように返す（等価）。
_UNPAIRED_CASES = {
    "stack_input": lambda: (_stack_input(), _stack_input()),
    "param_plus_stack_input": lambda: (
        Expression.binary_op("INT_ADD", _param(), _stack_input()),
        Expression.binary_op("INT_ADD", _param(), _stack_input()),
    ),
    "stack_input_without_storage": lambda: (_stack_input(storage=None), _stack_input(storage=None)),
    "non_parameter_register": lambda: (
        _stack_input("unaff_RBX", storage="register"), _stack_input("unaff_RBX", storage="register"),
    ),
}


@contextmanager
def _strategy(name):
    """checker の strategy を固定する（既定は pairwise。monolithic は直接選ぶ）。"""

    from scripts.function_tracer_pcode.checker import EquivalenceChecker

    if name == "pairwise":
        yield
        return
    original = EquivalenceChecker.__init__

    def init(self, *args, **kwargs):
        kwargs["strategy"] = name
        original(self, *args, **kwargs)

    EquivalenceChecker.__init__ = init
    try:
        yield
    finally:
        EquivalenceChecker.__init__ = original


#: 選んだ strategy が実際に最初の段として走ったことの確認に使う。
_FIRST_STAGE = {"pairwise": "S_PAIRWISE", "monolithic": "S_MONOLITHIC_FALLBACK"}


def _run(case_id, strategy, left, right):
    with _strategy(strategy):
        return run_production_check(f"u21-{strategy}-{case_id}", _side("f", left), _side("g", right))


def _strings(value):
    if isinstance(value, dict):
        for item in value.values():
            yield from _strings(item)
    elif isinstance(value, (list, tuple)):
        for item in value:
            yield from _strings(item)
    elif isinstance(value, str):
        yield value


def _unpaired_refs(result):
    return sorted({
        text for reason in result.get("unknown_reasons") or () for text in _strings(reason)
        if text.startswith(_REF)
    })


def _active(result):
    return sorted({str(row.get("reason_id")) for row in result.get("c_active_base") or ()})


@pytest.mark.parametrize("strategy", ["pairwise", "monolithic"])
@pytest.mark.parametrize("case_id", sorted(_UNPAIRED_CASES))
def test_sat_on_an_input_no_relation_covers_is_not_a_disequivalence(case_id, strategy):
    """修正前は 4 ケースとも両 strategy で最終 NOT_EQ（SMT は SAT、model は左右別の値）。"""

    left, right = _UNPAIRED_CASES[case_id]()
    result = _run(case_id, strategy, left, right)
    assert result["stage_path"][0] == _FIRST_STAGE[strategy], result["stage_path"]
    assert result["final_outcome"] == "UNKNOWN", (result["final_outcome"], _active(result))
    assert COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN in _active(result)
    refs = _unpaired_refs(result)
    assert refs and all(ref.split(":")[2] in {LEFT, RIGHT} for ref in refs), refs


def test_equal_parameter_returns_stay_equivalent():
    """対照: relation が覆う parameter だけの UNSAT は EQ のまま（規則は SAT 側だけ）。"""

    result = _run("param_equal", "pairwise", _param(), _param())
    assert result["final_outcome"] == "EQUIVALENT", _active(result)


@pytest.mark.parametrize("strategy", ["pairwise", "monolithic"])
def test_parameter_only_disequivalence_stays_not_eq(strategy):
    """対照: relation が覆う parameter だけの SAT（``n`` と ``n + 1``）は NOT_EQ のまま。"""

    right = Expression.binary_op("INT_ADD", _param(), Expression.constant(1, 4))
    result = _run("param_vs_successor", strategy, _param(), right)
    assert result["stage_path"][0] == _FIRST_STAGE[strategy], result["stage_path"]
    assert result["final_outcome"] == "NOT_EQ", _active(result)
    assert not _unpaired_refs(result)


def _parameter(name, index, bits=32):
    return ParameterInfo(original_name=name, smt_name=f"{name}_x", bit_width=bits, index=index)


def _relation(left="a", right="b", *, sufficient=True):
    """parameter 1 組の relation（``sufficient`` はその組の十分性）。"""

    return InputCorrespondenceSet(
        correspondences=(
            InputCorrespondence(
                left=SideParameter(0, 32, left), right=SideParameter(0, 32, right),
                kind=InputRelationKind.FULL_REGISTER_EQUALITY, rule="R0", tie_bits=32, entailed=(),
                decisive_sufficient=sufficient,
            ),
        ),
        left_parameter_count=1,
        right_parameter_count=1,
        left_parameters=(_parameter(left, 0),),
        right_parameters=(_parameter(right, 0),),
    )


def _free(name):
    return SimpleNamespace(original_name=name)


def _gate(free1, free2, correspondence):
    return CheckStrategy._unpaired_input_unsafety_reasons(
        SimpleNamespace(), free1, free2, query_correspondence=correspondence,
    )


def test_relation_covers_its_parameters_only():
    correspondence = _relation()
    assert correspondence.covered_input_names(LEFT) == frozenset({"a"})
    assert correspondence.covered_input_names(RIGHT) == frozenset({"b"})
    with pytest.raises(ValueError):
        correspondence.covered_input_names("middle")


def test_an_insufficient_relation_covers_nothing():
    assert _relation(sufficient=False).covered_input_names(LEFT) == frozenset()
    tie_only = build_tie_only_correspondence_set([_parameter("a", 0)], [_parameter("b", 0)])
    assert tie_only.covered_input_names(LEFT) == frozenset()


def test_gate_names_every_uncovered_free_input_per_side():
    correspondence = _relation()
    assert _gate([], [], correspondence) == []
    # relation が覆う記号は対象外（記号を共有する仕組みはこの集合を広げる）。
    assert _gate([_free("a")], [_free("b")], correspondence) == []
    assert _gate([_free("in_stack_8"), _free("in_stack_8")], [_free("unaff_RBX")], correspondence) == [
        "pair:unpaired_input:left:in_stack_8",
        "pair:unpaired_input:right:unaff_RBX",
    ]
    # 左右で同じ名前でも、左の parameter 名は右の記号を覆わない。
    assert _gate([], [_free("a")], correspondence) == ["pair:unpaired_input:right:a"]


def test_gate_is_fail_closed_without_the_query_record():
    correspondence = _relation()
    assert _gate(None, [], correspondence) == ["pair:unpaired_input:unavailable:left"]
    # relation が無ければ何も覆われない。
    assert _gate([_free("a")], [], None) == ["pair:unpaired_input:left:a"]


def test_unpaired_input_blocker_is_analysis_unsafety_that_replay_cannot_resolve():
    ref = "pair:unpaired_input:left:in_stack_8"
    blocker = classify_sat_safety_blocker(COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN, (ref,))
    assert blocker.resolution is SatSafetyResolution.ANALYSIS_UNSAFETY
    assert not blocker.replay_resolvable and not blocker.completable
    assert not replay_may_resolve_sat_safety_reason(
        COUNTEREXAMPLE_ANALYSIS_SAFETY_UNPROVEN, (ref, "counterexample_replay_missing"),
    )
