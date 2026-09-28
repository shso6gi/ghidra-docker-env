# -*- coding: utf-8 -*-
"""Issue #185: 入力領域の正本（封印した raw baseline）だけが入力の十分性を与える。

provenance ≠ proof: 型仮説の台帳・synthetic の名乗り・登録・名前の一致・現在の parameter 表は
どれも「どこから来たか」の記録で、元の関数の入力領域の証明ではない。十分性を認めるのは

* 公開境界で封印した raw baseline に、その index がちょうど 1 つあり、
* SMT が使う (幅, 符号) が baseline と一致し、
* 仮説の台帳に記録が無く、
* R1〜R5 のどれかを満たす

ときだけ。欠落・曖昧さ・仮説・証明できない synthetic 対応からは EQ / NOT_EQ を決めない。

T1 / T2 / T11b / T11b' の main での結果（修正前、同じ fixture を本 PR の base
``11d0998`` で実行）: T1 = final EQUIVALENT、T2 = final EQUIVALENT、T11b = True / True / False、
T11b' = EQUIVALENT / EQUIVALENT / NOT_EQ。どれも偽（fixture の docstring に反例）。
"""

from __future__ import annotations

import ast
from dataclasses import replace
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.core import Condition, Expression, ReturnInfo
from scripts.function_tracer_pcode.core.analysis import (
    DeferredCallInfo,
    FunctionReturnAnalysis,
    publish_raw_function_analysis,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.parameter_domain import (
    ParameterDomain,
    ParameterDomainHypothesis,
    ParameterDomainSealError,
    RawParameterDomains,
)
from scripts.function_tracer_pcode.core.signature import ResolvedTypeSpec, SignatureHypothesis
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    InputCorrespondenceStatus,
    build_input_correspondence_set,
    build_tie_only_correspondence_set,
)
from scripts.function_tracer_pcode.proof.formula.params import collect_param_info
from scripts.function_tracer_pcode.proof.recursive_abstraction import abstract_recursive_calls
from scripts.function_tracer_pcode.tests.conftest import create_mock_data_type_manager, resolve_mock_data_type
from scripts.function_tracer_pcode.tests.unit._production_check_harness import (
    call_effect_manifest_failure,
    has_no_synthetic_parameter,
    publish_like_the_analyzer,
    run_production_check,
    run_recursive_abstraction_branch,
)
from scripts.function_tracer_pcode.tests.unit.test_void_effect_only_return_abi_issue104 import _abi_facts


PACKAGE_ROOT = Path(__file__).resolve().parents[2]
AARCH64 = "AARCH64:LE:64:v8A"
MIPS64 = "MIPS:BE:64:64-32addr"
_DTM = create_mock_data_type_manager()


# ---------------------------------------------------------------------------
# fixtures（合成。EqBench の ground truth ではない）
# ---------------------------------------------------------------------------


def _param(name, size, data_type, *, index=0):
    return Expression.parameter(name, index, data_type=data_type, size=size)


def _const(value, size):
    return Expression.constant(value, size=size)


def _cmp(operator, left, right):
    return Expression.binary_op(operator, left, right)


def _descriptor(name, size, data_type, signed, *, index=0, **extra):
    return {
        "name": name, "index": index, "size": size, "data_type": data_type, "is_signed": signed,
        "data_type_obj": resolve_mock_data_type(data_type, _DTM), **extra,
    }


def _analysis(name, parameters, returns, *, function_ref=None):
    """解析器が作った（公開前の）解析。公開・封印は harness / ``publish_raw_function_analysis`` が行う。"""

    analysis = FunctionReturnAnalysis(
        function_name=name, entry_point="0x1000", parameters=parameters, returns=returns,
        return_type="int", function_ref=function_ref, binary_id=f"bin-{name}",
    )
    analysis.return_abi_facts = _abi_facts(return_type="/int", type_length=4, storage="PRESENT")
    return analysis


def _raw(name, parameters, returns=None, **kwargs):
    returns = returns if returns is not None else [ReturnInfo("0x10", _const(0, 4), [])]
    return publish_raw_function_analysis(_analysis(name, parameters, returns, **kwargs))


def _two_way(value_if, value_else, condition):
    return [
        ReturnInfo("0x10", _const(value_if, 4), [condition]),
        ReturnInfo("0x20", _const(value_else, 4), [Condition(condition.expression, True)]),
    ]


def _p1_pair():
    """loop2 B4_B16 の形（Issue #185 AC1）。

    left (arm64): ``int f(int x) { return x < 10; }``。
    right (mips64): ``f(ulong p) { return (int)p < 10 && p != 0x100000005; }``。
    right は上位 bit を読む（P0 は ``wide_side_not_closed`` で UNKNOWN）。P1 の usage hint が
    ``ulong -> int`` を仮定すると p の leaf が 32 bit に縮み、上位 bit の比較が消える。
    反例: p = 0x100000005 で left(5) = 1、right = 0（EQ は偽）。
    """

    x = _param("param_1", 4, "int")
    left = _analysis("left", [_descriptor("param_1", 4, "int", True)], _two_way(1, 0, Condition(_cmp("INT_SLESS", x, _const(10, 4)))))
    p = _param("param_1", 8, "ulong")
    low = Expression.binary_op("SUBPIECE", p, _const(0, 4))
    low.size = 4
    low_lt = Condition(_cmp("INT_SLESS", low, _const(10, 4)))
    high = Condition(_cmp("INT_NOTEQUAL", p, _const(0x100000005, 8)))
    right = _analysis(
        "right",
        [_descriptor("param_1", 8, "ulong", False)],
        [
            ReturnInfo("0x10", _const(1, 4), [low_lt, high]),
            ReturnInfo("0x20", _const(0, 4), [Condition(low_lt.expression, True)]),
            ReturnInfo("0x30", _const(0, 4), [low_lt, Condition(high.expression, True)]),
        ],
    )
    return left, right


def _p4a_pair():
    """P4A の ``long -> uint``（usage hint 無し）。

    left (arm64): ``int f(uint x) { return x < 10; }``。right (mips64): ``f(long p) { return p < 10; }``
    （符号付き 64 bit の比較）。P4A が ``long -> unsigned int`` を仮定すると比較が符号なし
    32 bit に反転する。反例: p = -1 で right = 1、left(0xffffffff) = 0（EQ は偽）。
    """

    x = _param("param_1", 4, "uint")
    left = _analysis("left", [_descriptor("param_1", 4, "uint", False)], _two_way(1, 0, Condition(_cmp("INT_LESS", x, _const(10, 4)))))
    p = _param("param_1", 8, "long")
    right = _analysis("right", [_descriptor("param_1", 8, "long", True)], _two_way(1, 0, Condition(_cmp("INT_SLESS", p, _const(10, 8)))))
    return left, right


def _self_target(name):
    return CallTargetRef.from_name(name, program_id=sum(map(ord, name)) & 0xFFFFFFFF, entry_offset=0x401000)


def _recursive(side, pname, argument, combine, *, base_case=True):
    """``f(n) = n <= 0 ? 0 : combine(f(argument(n)))``（自己再帰を deferred call で残した解析）。"""

    n = _param(pname, 4, "int")
    placeholder = f"call_out_of_scope:{side}#0"
    info = DeferredCallInfo(placeholder, _self_target(side), [argument(n)], sequence=0)
    unknown = Expression.unknown(placeholder, runtime_ref=info.unknown_ref)
    unknown.size = 4
    base = Condition(_cmp("INT_SLESSEQUAL", n, _const(0, 4)))
    returns = [ReturnInfo("0x10", combine(unknown), [Condition(base.expression, True)] if base_case else [])]
    if base_case:
        returns.append(ReturnInfo("0x20", _const(0, 4), [base]))
    analysis = _analysis(side, [_descriptor(pname, 4, "int", True)], returns, function_ref=_self_target(side))
    analysis.deferred_calls = {placeholder: info}
    return analysis


def _minus_one(n):
    return _cmp("INT_SUB", n, _const(1, 4))


def _plus_one(value):
    return _cmp("INT_ADD", value, _const(1, 4))


#: 抽象化の分岐が決める 3 つの形（Issue #185 T11b）。どれも要約変数（帰納法の仮定）が証明されない。
#: A1: ``f(n) = f(n-1) + 1``（両側、停止しない再帰。抽象化は EQ）。
#: A2: 引数が構造として等しいだけ（``n+1`` と ``1+m``。抽象化は EQ）。
#: A3: ``f(n) = n<=0 ? 0 : f(n-1)`` と ``g(n) = n<=0 ? 0 : 2*g(n-1)``: どちらも常に 0 で等価だが、
#:     要約変数が自由なので抽象化は NOT_EQ（偽の NOT_EQ）。
_ABSTRACTION_CASES = {
    "A1": lambda: (
        _recursive("left", "n", _minus_one, _plus_one, base_case=False),
        _recursive("right", "m", _minus_one, _plus_one, base_case=False),
    ),
    "A2": lambda: (
        _recursive("left", "n", lambda n: _cmp("INT_ADD", n, _const(1, 4)), _plus_one),
        _recursive("right", "m", lambda n: _cmp("INT_ADD", _const(1, 4), n), _plus_one),
    ),
    "A3": lambda: (
        _recursive("left", "n", _minus_one, lambda value: value),
        _recursive("right", "m", _minus_one, lambda value: _cmp("INT_MULT", value, _const(2, 4))),
    ),
}


def _relation(analysis1, analysis2):
    return build_input_correspondence_set(analysis1, analysis2)


def _evidence(relation):
    return "\n".join(relation.insufficiency_evidence())


def _reason_text(result):
    """最終結果の UNKNOWN の理由と、各 attempt の理由の集約（retry の phase の理由はここに残る）。"""

    import json

    return json.dumps(
        {key: result.get(key) for key in ("unknown_reasons", "unknown_cause_aggregate")}, default=str,
    )


def _hypothesis(position, type_name, size, signed, *, phase, source="test_hint"):
    spec = ResolvedTypeSpec(type_name=type_name, data_type_obj=None, size_bytes=size, is_signed=signed, source=source)
    return SignatureHypothesis(
        parameter_type_overrides={position: type_name},
        resolved_parameter_overrides={position: spec},
        phase=phase,
        reason="test hypothesis",
    )


def _int_pair():
    left = _raw("left", [_descriptor("a", 4, "int", True)])
    right = _raw("right", [_descriptor("a", 4, "int", True)])
    return left, right


# ---------------------------------------------------------------------------
# T1 / T2: 仮説の下の EQ は final にならない（AC1）
# ---------------------------------------------------------------------------


def test_t1_p1_usage_hint_hypothesis_does_not_reach_final_equivalent():
    left, right = _p1_pair()
    result = run_production_check("t1-p1", left, right, left_architecture=AARCH64, right_architecture=MIPS64)

    # 仮説が本当に適用された（空振りで通る test にしない）
    applied = result["function2_signature_hypotheses"]
    assert [item.get("phase") for item in applied] == ["P1_SIGNEDNESS"], applied
    assert result["final_outcome"] not in {"EQUIVALENT", "NOT_EQ"}, result["final_outcome"]
    assert result["final_outcome"] == "UNKNOWN"
    assert "right:parameter_domain_hypothesis:P1_SIGNEDNESS:u64->s32" in _reason_text(result)


def test_t2_p4a_abi_hypothesis_without_hint_does_not_reach_final_equivalent():
    left, right = _p4a_pair()
    result = run_production_check("t2-p4a", left, right, left_architecture=AARCH64, right_architecture=MIPS64)

    applied = result["function2_signature_hypotheses"]
    assert [item.get("phase") for item in applied] == ["P4A_MIPS64_ABI"], applied
    assert result["final_outcome"] == "UNKNOWN", result["final_outcome"]
    assert "right:parameter_domain_hypothesis:P4A_MIPS64_ABI:s64->u32" in _reason_text(result)


# ---------------------------------------------------------------------------
# T3〜T8, T10: 正本・台帳・複製の契約
# ---------------------------------------------------------------------------


def test_t3_a_changed_table_without_a_ledger_record_is_insufficient():
    left, right = _int_pair()
    narrowed = right.semantic_successor(parameters=[_descriptor("a", 2, "short", True)])
    assert narrowed.parameter_domain_hypotheses == ()
    relation = _relation(left, narrowed)
    assert relation.status is InputCorrespondenceStatus.INSUFFICIENT
    assert "right:parameter_domain_changed:s32->s16" in _evidence(relation)

    # 台帳だけを消した overlay（記録の欠落）も、表が正本と違うので不十分
    overlay = right.with_signature_hypothesis(_hypothesis(0, "uint", 4, False, phase="P1_SIGNEDNESS"))
    dropped = replace(overlay, parameter_domain_hypotheses=())
    relation = _relation(left, dropped)
    assert not relation.decisive_sufficient
    assert "right:parameter_domain_changed:s32->u32" in _evidence(relation)


def test_t4_a_rebound_index_is_insufficient():
    left = _raw("left", [_descriptor("a", 4, "int", True, index=0), _descriptor("b", 8, "long", True, index=1)])
    right = _raw("right", [_descriptor("a", 4, "int", True, index=0), _descriptor("b", 8, "long", True, index=1)])
    assert _relation(left, right).decisive_sufficient

    swapped = right.semantic_successor(parameters=[
        _descriptor("a", 8, "long", True, index=0), _descriptor("b", 4, "int", True, index=1),
    ])
    evidence = _evidence(_relation(left, swapped))
    assert "parameter_domain_changed:s32->s64" in evidence
    assert "parameter_domain_changed:s64->s32" in evidence

    renamed = right.semantic_successor(parameters=[
        _descriptor("a", 4, "int", True, index=0), _descriptor("b", 8, "long", True, index=7),
    ])
    relation = _relation(left, renamed)
    assert not relation.decisive_sufficient
    assert "right:parameter_domain_origin_unmatched:7" in _evidence(relation)
    assert "parameter_domain_origin_dropped:right:1" in relation.structural_defects


@pytest.mark.parametrize(
    "parameters, uncertified, unindexed",
    [
        ([_descriptor("a", 4, "int", True, index=0), _descriptor("b", 4, "int", True, index=0)], (0,), 0),
        ([{"name": "a", "size": 4, "is_signed": True}], (0,), 0),
        ([{"name": "a", "index": -1, "size": 4, "is_signed": True}], (-1,), 0),
        ([{"name": "a", "index": "zero", "size": 4, "is_signed": True}], (), 1),
        ([{"name": "a", "index": True, "size": 4, "is_signed": True}], (), 1),
        ([{"name": "a", "index": 0, "size": None, "is_signed": True}], (0,), 0),
    ],
    ids=["duplicate", "implicit-index", "negative", "non-integer", "bool", "unreadable-width"],
)
def test_t5_duplicate_or_missing_indices_are_sealed_as_uncertified(parameters, uncertified, unindexed):
    analysis = _analysis("left", parameters, [ReturnInfo("0x10", _const(0, 4), [])])
    analysis.seal_raw_parameter_domains()
    baseline = analysis.raw_parameter_domains
    assert baseline.certified == ()
    assert baseline.uncertified == uncertified
    assert baseline.unindexed == unindexed


def test_t5_uncertified_index_never_gives_sufficiency():
    duplicated = [_descriptor("a", 4, "int", True, index=0), _descriptor("b", 4, "int", True, index=0)]
    left = _raw("left", [_descriptor("a", 4, "int", True, index=0)])
    right = _raw("right", duplicated)
    relation = _relation(left, right)
    assert not relation.decisive_sufficient
    assert "right:parameter_domain_origin_unmatched:0" in _evidence(relation)


def test_t5_seal_contract_rejects_resealing_and_forged_baselines():
    analysis = _raw("left", [_descriptor("a", 4, "int", True)])
    with pytest.raises(ParameterDomainSealError, match="already_sealed"):
        analysis.seal_raw_parameter_domains()
    with pytest.raises(ParameterDomainSealError, match="sealed_only_at_publication"):
        RawParameterDomains(certified=((0, ParameterDomain(32, True)),))
    # 封印の印は constructor の引数ではないので、写し（replace）でも持ち越せない
    with pytest.raises(ParameterDomainSealError, match="sealed_only_at_publication"):
        replace(analysis.raw_parameter_domains, certified=((0, ParameterDomain(64, True)),))
    # 派生の API は正本・台帳を差し替えない
    for field_name, value in (("raw_parameter_domains", None), ("parameter_domain_hypotheses", ())):
        with pytest.raises(ValueError, match="input-domain authority"):
            analysis.semantic_successor(**{field_name: value})
    # 公開境界は cache が返した封印済みの解析を封印し直さない（最初の封印が正本のまま）
    baseline = analysis.raw_parameter_domains
    assert publish_raw_function_analysis(analysis).raw_parameter_domains is baseline


def test_t6_a_hypothesis_chain_keeps_the_seal_time_baseline_and_ledgers_every_step():
    left, right = _int_pair()
    baseline = right.raw_parameter_domains
    first = right.with_signature_hypothesis(_hypothesis(0, "long", 8, True, phase="P1_SIGNEDNESS", source="param_semantic_hint"))
    second = first.with_signature_hypothesis(_hypothesis(0, "uint", 4, False, phase="P4A_MIPS64_ABI"))
    assert second.raw_parameter_domains is baseline
    assert second.parameter_domain_hypotheses == (
        ParameterDomainHypothesis(0, ParameterDomain(32, True), ParameterDomain(64, True), "P1_SIGNEDNESS", "param_semantic_hint"),
        ParameterDomainHypothesis(0, ParameterDomain(64, True), ParameterDomain(32, False), "P4A_MIPS64_ABI", "test_hint"),
    )
    evidence = _evidence(_relation(left, second))
    assert "right:parameter_domain_changed:s32->u32" in evidence

    # 往復（現在の表が正本に戻っても、仮説を経た式は正本の式ではない）
    back = first.with_signature_hypothesis(_hypothesis(0, "int", 4, True, phase="P2_PATTERN_INT"))
    assert [(entry.before, entry.after) for entry in back.parameter_domain_hypotheses] == [
        (ParameterDomain(32, True), ParameterDomain(64, True)),
        (ParameterDomain(64, True), ParameterDomain(32, True)),
    ]
    relation = _relation(left, back)
    assert not relation.decisive_sufficient
    evidence = _evidence(relation)
    assert "parameter_domain_changed" not in evidence
    assert "right:parameter_domain_hypothesis:P1_SIGNEDNESS:s32->s64" in evidence


def test_t7_rebuilt_or_copied_analyses_without_the_seal_have_no_authority():
    left, right = _int_pair()
    rebuilt = FunctionReturnAnalysis(
        function_name=right.function_name, entry_point=right.entry_point,
        parameters=[dict(param) for param in right.parameters], returns=list(right.returns),
    )
    relation = _relation(left, rebuilt)
    assert relation.status is InputCorrespondenceStatus.INSUFFICIENT
    assert "parameter_domain_origin_unavailable:right" in relation.structural_defects
    assert "right:parameter_domain_origin_unavailable" in _evidence(relation)

    stripped = replace(right, raw_parameter_domains=None)
    assert not _relation(left, stripped).decisive_sufficient

    # 封印を持つ複製・派生（semantic_successor / 派生 view）は同じ正本を引き継ぐ
    for copy in (right.semantic_successor(), right.with_accepted_return_partition(list(right.returns))):
        assert copy.raw_parameter_domains is right.raw_parameter_domains
        assert _relation(left, copy).status is InputCorrespondenceStatus.COMPLETE

    # 0 parameter 同士（EMPTY）も「入力が 0 個」は正本で証明される主張
    empty_left, empty_right = _raw("left", []), _raw("right", [])
    assert _relation(empty_left, empty_right).status is InputCorrespondenceStatus.EMPTY
    assert _relation(empty_left, replace(empty_right, raw_parameter_domains=None)).status is (
        InputCorrespondenceStatus.INSUFFICIENT
    )


def test_t8_selective_reanalysis_replays_onto_a_fresh_seal_and_recomputes_the_ledger(monkeypatch):
    from scripts.function_tracer_pcode.checker.phases.handler import PhaseContext, PhaseResult, PhaseID
    from scripts.function_tracer_pcode.checker.reanalysis import selective_reanalysis_and_check
    from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
    from scripts.function_tracer_pcode.tests.conftest import MockProgram

    left_template, right_template = _p1_pair()
    cached_left = publish_like_the_analyzer(left_template)
    cached_right = publish_like_the_analyzer(right_template).with_signature_hypothesis(
        _hypothesis(0, "int", 4, True, phase="P1_SIGNEDNESS", source="param_semantic_hint")
    )
    produced = []

    class Analyzer:
        def __init__(self, program, **_kwargs):
            self._program = program

        def analyze_function_by_name(self, _name, _timeout):
            fresh = publish_like_the_analyzer(right_template)
            produced.append(fresh)
            return fresh

        def refresh_structural_recurrence_summary(self, analysis, **_kwargs):
            return analysis

        def dispose(self):
            pass

    captured = {}

    class Checker:
        debug = False
        analyzer_factory = Analyzer

        def _debug_print(self, *_args):
            pass

        def _run_stage_plan(self, analysis1, analysis2, *_args, **_kwargs):
            captured["pair"] = (analysis1, analysis2)
            return None

    program1, program2 = MockProgram("left", AARCH64), MockProgram("right", MIPS64)
    ctx = PhaseContext(
        program1=program1, program2=program2, function_name1="f", function_name2="f",
        binary1_name="left", binary2_name="right", decompile_timeout=10, save_formula=False,
        type_fix_result=TypeFixResult(), original_signature1=None, original_signature2=None,
    )
    ctx.analysis1, ctx.analysis2 = cached_left, cached_right
    selective_reanalysis_and_check(
        Checker(), ctx,
        PhaseResult(PhaseID.P1_SIGNEDNESS, applied=True, retry_name="x", changed_binary1=False, changed_binary2=True),
        1,
    )
    replayed = captured["pair"][1]
    assert replayed is not cached_right
    assert replayed.raw_parameter_domains is produced[0].raw_parameter_domains
    assert replayed.parameter_domain_hypotheses == cached_right.parameter_domain_hypotheses
    relation = _relation(captured["pair"][0], replayed)
    assert not relation.decisive_sufficient
    assert "right:parameter_domain_hypothesis:P1_SIGNEDNESS:u64->s32" in _evidence(relation)


def test_t10_a_hypothesis_view_cannot_be_sealed_as_raw():
    unsealed = _analysis("right", [_descriptor("a", 4, "int", True)], [ReturnInfo("0x10", _const(0, 4), [])])
    overlay = unsealed.with_signature_hypothesis(_hypothesis(0, "uint", 4, False, phase="P1_SIGNEDNESS"))
    with pytest.raises(ParameterDomainSealError, match="hypothesis_view"):
        overlay.seal_raw_parameter_domains()
    with pytest.raises(ParameterDomainSealError, match="hypothesis_view"):
        publish_raw_function_analysis(overlay)
    # return だけの仮説の view も「仮説の後」なので正本にならない
    return_only = unsealed.with_signature_hypothesis(SignatureHypothesis(return_type_override="uint", phase="P2_PATTERN_INT"))
    with pytest.raises(ParameterDomainSealError, match="hypothesis_view"):
        return_only.seal_raw_parameter_domains()


# ---------------------------------------------------------------------------
# T9: 入力領域を変えない仮説は decisive のまま（AC2 の対照）
# ---------------------------------------------------------------------------


def test_t9_metadata_only_and_return_only_hypotheses_keep_the_relation_decisive():
    left, right = _int_pair()
    renamed = right.with_signature_hypothesis(_hypothesis(0, "int32_t", 4, True, phase="P3_PARAM_TYPE"))
    assert renamed.parameters[0]["data_type"] == "int32_t"
    assert renamed.parameter_domain_hypotheses == ()
    assert _relation(left, renamed).status is InputCorrespondenceStatus.COMPLETE

    returned = right.with_signature_hypothesis(SignatureHypothesis(return_type_override="uint", phase="P2_PATTERN_INT"))
    assert returned.signature_hypotheses and returned.parameter_domain_hypotheses == ()
    assert _relation(left, returned).status is InputCorrespondenceStatus.COMPLETE


def test_t9_the_raw_pair_keeps_its_decisive_equivalent_end_to_end():
    x = _param("param_1", 4, "int")
    condition = Condition(_cmp("INT_SLESS", x, _const(10, 4)))
    left = _analysis("left", [_descriptor("param_1", 4, "int", True)], _two_way(1, 0, condition))
    right = _analysis("right", [_descriptor("param_1", 4, "int", True)], _two_way(1, 0, condition))
    result = run_production_check("t9-raw", left, right, left_architecture=AARCH64, right_architecture=MIPS64)
    assert result["final_outcome"] == "EQUIVALENT", _reason_text(result)


# ---------------------------------------------------------------------------
# T11: synthetic parameter（abstraction）は対応を証明しない
# ---------------------------------------------------------------------------


def test_t11a_abstracted_pair_relation_is_insufficient_for_one_or_reordered_synthetics():
    left_template, right_template = _ABSTRACTION_CASES["A1"]()
    left, right = publish_like_the_analyzer(left_template), publish_like_the_analyzer(right_template)
    abstraction = abstract_recursive_calls(left, right)
    assert abstraction.applied
    relation = _relation(abstraction.analysis1, abstraction.analysis2)
    assert relation.status is InputCorrespondenceStatus.INSUFFICIENT
    evidence = _evidence(relation)
    assert "left:synthetic_parameter_correspondence_unproven:synthetic_recursive_summary:10000" in evidence
    assert "right:synthetic_parameter_correspondence_unproven:synthetic_recursive_summary:10000" in evidence

    # 2 つの synthetic を逆順に並べても（名前で pairing される）対応は証明されない
    def with_two(analysis, order):
        extra = [
            {"name": f"summary_rec_{10000 + i}", "index": 10000 + i, "size": 4, "data_type": "int",
             "is_signed": True, "synthetic_recursive_summary": True}
            for i in order
        ]
        return analysis.semantic_successor(parameters=list(analysis.parameters) + extra)

    relation = _relation(with_two(left, (0, 1)), with_two(right, (1, 0)))
    assert not relation.decisive_sufficient
    assert _evidence(relation).count("synthetic_parameter_correspondence_unproven") >= 4


@pytest.mark.parametrize("case", sorted(_ABSTRACTION_CASES))
def test_t11b_the_abstraction_branch_decides_nothing(case):
    left, right = _ABSTRACTION_CASES[case]()
    result = run_recursive_abstraction_branch("t11b-" + case, left, right)
    assert result is not None, "the abstraction must apply (otherwise the test is vacuous)"
    assert result.is_equivalent is None, (case, result.is_equivalent)
    assert "synthetic_parameter_correspondence_unproven:synthetic_recursive_summary:10000" in str(result.to_dict())


@pytest.mark.parametrize("case", sorted(_ABSTRACTION_CASES))
def test_t11b_prime_a_failed_raw_pair_manifest_does_not_let_the_abstraction_decide(case):
    left, right = _ABSTRACTION_CASES[case]()
    with call_effect_manifest_failure(has_no_synthetic_parameter) as injected:
        result = run_production_check("t11bp-" + case, left, right, left_architecture=AARCH64, right_architecture=AARCH64)
    assert injected, "the injection must hit the raw pair"
    assert "S_ABSTRACT_RECURSIVE_SUMMARY" in result["stage_path"]
    assert result["final_outcome"] == "UNKNOWN", (case, result["final_outcome"])


def test_t11c_a_really_equal_recursive_pair_is_unknown_with_traceable_evidence():
    left = _recursive("left", "n", _minus_one, _plus_one)
    right = _recursive("right", "m", _minus_one, _plus_one)
    result = run_recursive_abstraction_branch("t11c", left, right)
    assert result is not None and result.is_equivalent is None
    text = str(result.to_dict())
    assert "synthetic_parameter_correspondence_unproven:synthetic_recursive_summary:10000" in text


def test_t11d_a_one_sided_synthetic_is_insufficient():
    left, right = _int_pair()
    synthetic = {"name": "summary_rec_10000", "index": 10000, "size": 4, "data_type": "int",
                 "is_signed": True, "synthetic_recursive_summary": True}
    one_sided = right.semantic_successor(parameters=list(right.parameters) + [synthetic])
    relation = _relation(left, one_sided)
    assert not relation.decisive_sufficient
    # 相手の無い synthetic は R0（main でも不十分: 対照）
    assert "param[-,10000]:MISSING_SIDE" in _evidence(relation)


def test_t11e_a_forged_synthetic_flag_on_a_raw_parameter_gives_no_exemption():
    left, right = _int_pair()
    forged = right.semantic_successor(parameters=[dict(right.parameters[0], synthetic_recursive_summary=True)])
    relation = _relation(left, forged)
    assert not relation.decisive_sufficient
    assert "right:synthetic_parameter_correspondence_unproven:synthetic_recursive_summary:0" in _evidence(relation)
    # 正本に最初から flag 付きで入っていた記述子も同じ（名乗りは減らす方向にしか効かない）
    sealed_with_flag = _raw("right", [_descriptor("a", 4, "int", True, synthetic_recursive_summary=True)])
    assert not _relation(left, sealed_with_flag).decisive_sufficient


def test_t11f_a_width_mismatch_stays_insufficient():
    left = _raw("left", [_descriptor("a", 4, "int", True)], [ReturnInfo("0x10", _param("a", 4, "int"), [])])
    right = _raw("right", [_descriptor("a", 8, "long", True)], [ReturnInfo("0x10", _param("a", 8, "long"), [])])
    relation = _relation(left, right)
    assert not relation.decisive_sufficient
    assert "parameter_domain" not in _evidence(relation)


# ---------------------------------------------------------------------------
# T12: 封印の owner（静的）
# ---------------------------------------------------------------------------


_SEAL_NAMES = {
    "seal_raw_parameter_domains": {"core/analysis.py"},
    "seal_parameter_table": {"core/parameter_domain.py", "core/analysis.py"},
    "_SEAL": {"core/parameter_domain.py"},
    "publish_raw_function_analysis": {"core/analysis.py", "analysis/returns/lifecycle.py"},
    "RawParameterDomains": {"core/parameter_domain.py", "core/analysis.py"},
}


def _production_modules():
    for path in sorted(PACKAGE_ROOT.rglob("*.py")):
        relative = path.relative_to(PACKAGE_ROOT).as_posix()
        if relative.startswith("tests/"):
            continue
        yield relative, ast.parse(path.read_text(encoding="utf-8"), filename=relative)


def _references(tree):
    for node in ast.walk(tree):
        if isinstance(node, ast.Name):
            yield node.id, node
        elif isinstance(node, ast.Attribute):
            yield node.attr, node
        elif isinstance(node, ast.alias):
            yield (node.asname or node.name).split(".")[-1], node
            yield node.name.split(".")[-1], node
        elif isinstance(node, ast.keyword) and node.arg:
            yield node.arg, node


_AUTHORITY_FIELDS = ("raw_parameter_domains", "parameter_domain_hypotheses")
#: field 名を key とする表を持つ module（書き込みではない: snapshot の field 分類）
_FIELD_TABLE_MODULES = {"proof/obligations/snapshot.py"}


def _dynamic_writes(tree, *, mapping_allowed=False):
    """名前を文字列で渡す書き込み（``setattr(x, "<field>", ...)`` / ``__dict__["<field>"]`` / ``**{...}``）。

    ``mapping_allowed``: field 名を key に持つ表そのものが契約の module（snapshot の field 分類）。
    """

    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and getattr(node.func, "id", getattr(node.func, "attr", None)) in {
            "setattr", "__setattr__",
        }:
            if any(isinstance(arg, ast.Constant) and arg.value in _AUTHORITY_FIELDS for arg in node.args):
                yield node.lineno, "setattr of an input-domain authority field"
        if isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Constant):
            if node.slice.value in _AUTHORITY_FIELDS:
                yield node.lineno, "subscript write of an input-domain authority field"
        if isinstance(node, ast.Dict) and not mapping_allowed:
            if any(isinstance(key, ast.Constant) and key.value in _AUTHORITY_FIELDS for key in node.keys):
                yield node.lineno, "input-domain authority field passed through a mapping"


def test_t12_only_the_publication_boundary_seals_and_only_core_writes_the_baseline():
    offenders = []
    for relative, tree in _production_modules():
        for name, node in _references(tree):
            allowed = _SEAL_NAMES.get(name)
            if allowed is not None and relative not in allowed:
                offenders.append(f"{relative}:{getattr(node, 'lineno', '?')}:{name}")
            if name in _AUTHORITY_FIELDS and relative not in {"core/analysis.py", "core/parameter_domain.py"}:
                writes = (
                    isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Store)
                ) or isinstance(node, ast.keyword)
                if writes:
                    offenders.append(f"{relative}:{getattr(node, 'lineno', '?')}:writes {name}")
        offenders.extend(
            f"{relative}:{line}:{what}"
            for line, what in _dynamic_writes(tree, mapping_allowed=relative in _FIELD_TABLE_MODULES)
        )
    assert offenders == []
    # 公開境界は 1 箇所で実際にこの関数を呼んでいる（guard が空振りしない）
    lifecycle = dict(_production_modules())["analysis/returns/lifecycle.py"]
    calls = [
        node for node in ast.walk(lifecycle)
        if isinstance(node, ast.Call) and getattr(node.func, "id", None) == "publish_raw_function_analysis"
    ]
    assert len(calls) == 1


def test_t12_the_guard_catches_a_seal_outside_the_boundary(tmp_path):
    tree = ast.parse(
        "def f(a):\n"
        "    a.seal_raw_parameter_domains()\n"
        "    a.raw_parameter_domains = None\n"
        "    b = replace(a, parameter_domain_hypotheses=())\n"
        "    setattr(a, 'parameter_domain_hypotheses', ())\n"
        "    a.__dict__['raw_parameter_domains'] = None\n"
        "    replace(a, **{'raw_parameter_domains': None})\n"
    )
    names = [name for name, _node in _references(tree)]
    assert "seal_raw_parameter_domains" in names
    stores = [node for name, node in _references(tree) if name == "raw_parameter_domains" and isinstance(node.ctx, ast.Store)]
    assert len(stores) == 1
    keywords = [node for name, node in _references(tree) if name == "parameter_domain_hypotheses" and isinstance(node, ast.keyword)]
    assert len(keywords) == 1
    assert [what for _line, what in _dynamic_writes(tree)] == [
        "setattr of an input-domain authority field",
        "subscript write of an input-domain authority field",
        "input-domain authority field passed through a mapping",
    ]


def test_t12_one_reading_rule_for_the_formula_and_the_seal():
    """SMT の parameter 表と封印は同じ読み方（index の既定 0・size の既定 4 byte・符号の既定 signed）。"""

    descriptor = {"name": "p"}
    info = collect_param_info([descriptor], "_1")[0]
    analysis = _analysis("left", [descriptor], [ReturnInfo("0x10", _const(0, 4), [])])
    analysis.seal_raw_parameter_domains()
    # index の書かれていない記述子は 0 と読まれるが、明示されていないので認証しない
    assert (info.index, info.bit_width, info.is_signed) == (0, 32, True)
    assert analysis.raw_parameter_domains.uncertified == (0,)


# ---------------------------------------------------------------------------
# T13: tie-only の補助 relation は decisive にならない
# ---------------------------------------------------------------------------


def test_t13_a_tie_only_relation_is_never_decisive_and_cannot_stand_in_for_the_final_relation():
    from scripts.function_tracer_pcode.proof.strategies.proof_gates.sat_safety import (
        _impl__input_correspondence_unsafety_reasons,
    )

    left, right = _int_pair()
    infos1 = collect_param_info(list(left.parameters), "_1")
    infos2 = collect_param_info(list(right.parameters), "_2")
    tie_only = build_tie_only_correspondence_set(infos1, infos2)
    assert not tie_only.decisive_sufficient
    assert "parameter_domain_origin_unavailable:left" in tie_only.structural_defects
    # premise（tie）は描ける: UNSAT 側の補助証明には使える
    assert any(line.startswith("(assert (= a_1 a_2))") for line in tie_only.premise_lines(infos1, infos2))

    # 決定の authority は raw pair の最終 relation だけ: 仮説の下の relation は、query が同じ
    # relation でも十分性の欠陥を理由として返す（tie-only は authority に使われない）
    overlay = right.with_signature_hypothesis(_hypothesis(0, "uint", 4, False, phase="P1_SIGNEDNESS"))
    authority = _relation(left, overlay)
    reasons = _impl__input_correspondence_unsafety_reasons(None, authority, authority_correspondence=authority)
    assert any("right:parameter_domain_hypothesis:P1_SIGNEDNESS:s32->u32" in reason for reason in reasons)
    raw_authority = _relation(left, right)
    assert _impl__input_correspondence_unsafety_reasons(None, raw_authority, authority_correspondence=raw_authority) == []


# ---------------------------------------------------------------------------
# 監査の独立した oracle と serialization
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "mutate, expected",
    [
        (lambda a: a, ()),
        (lambda a: a.semantic_successor(parameters=[_descriptor("a", 4, "int", False)]), ("parameter_domain_changed:s32->u32",)),
        (lambda a: a.semantic_successor(parameters=[_descriptor("a", 8, "long", True)]), ("parameter_domain_changed:s32->s64",)),
        (lambda a: replace(a, raw_parameter_domains=None), ("parameter_domain_origin_unavailable",)),
        (
            lambda a: a.with_signature_hypothesis(_hypothesis(0, "uint", 4, False, phase="P1_SIGNEDNESS")),
            ("parameter_domain_changed:s32->u32", "parameter_domain_hypothesis:P1_SIGNEDNESS:s32->u32"),
        ),
    ],
    ids=["raw", "sign", "width", "unsealed", "hypothesis"],
)
def test_the_right_side_defects_are_exactly_the_expected_ones(mutate, expected):
    left, right = _int_pair()
    relation = _relation(left, mutate(right))
    right_refs = tuple(
        ref[len("right:"):]
        for item in relation.correspondences
        for ref in item.evidence
        if ref.startswith("right:parameter_domain") or ref.startswith("right:synthetic")
    )
    assert right_refs == expected
    assert relation.decisive_sufficient is (expected == ())


def test_serialization_reports_the_baseline_only_when_it_differs_and_the_ledger_only_when_present():
    left, right = _int_pair()
    raw_dict = right.to_dict()
    assert "raw_parameter_domains" not in raw_dict and "parameter_domain_hypotheses" not in raw_dict

    overlay = right.with_signature_hypothesis(_hypothesis(0, "uint", 4, False, phase="P1_SIGNEDNESS", source="param_semantic_hint"))
    overlay_dict = overlay.to_dict()
    assert overlay_dict["raw_parameter_domains"] == {"certified": [[0, 32, True]], "uncertified": [], "unindexed": 0}
    assert overlay_dict["parameter_domain_hypotheses"] == [
        {"index": 0, "before": "s32", "after": "u32", "phase": "P1_SIGNEDNESS", "source": "param_semantic_hint"}
    ]

    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot

    # 台帳だけを消して表を正本へ戻した view と raw は、正本の差分が無いので fingerprint が同じ。
    # 台帳のある view は別の前提
    # 台帳・正本の差分は解析前提の同一性に入る: 同じ表・同じ式でも台帳の有無で別の前提
    ledger_only = replace(right, parameter_domain_hypotheses=overlay.parameter_domain_hypotheses)
    assert AnalysisSnapshot.from_function_analysis(ledger_only).semantic_fingerprint != (
        AnalysisSnapshot.from_function_analysis(right).semantic_fingerprint
    )
    diverged = right.semantic_successor(parameters=[_descriptor("a", 4, "int", False)])
    assert "raw_parameter_domains" in diverged.to_dict()
    assert AnalysisSnapshot.from_function_analysis(diverged).semantic_fingerprint != (
        AnalysisSnapshot.from_function_analysis(replace(diverged, raw_parameter_domains=None)).semantic_fingerprint
    )


def test_a_rebuilt_relation_over_a_changed_table_is_insufficient():
    """作り直し（certificate の独立検査）が古い parameter 表を使っても、いまの表が正本と違えば不十分。"""

    from scripts.function_tracer_pcode.proof.formula.input_correspondence.relation import (
        rebuild_input_correspondence_set,
    )

    left, right = _int_pair()
    previous = _relation(left, right)
    assert previous.decisive_sufficient
    changed = right.semantic_successor(parameters=[_descriptor("a", 4, "int", False)])
    rebuilt = rebuild_input_correspondence_set(previous, left, changed)
    assert not rebuilt.decisive_sufficient
    assert "right:parameter_domain_changed:s32->u32" in _evidence(rebuilt)


def test_an_unsealed_analysis_is_a_different_premise_from_the_sealed_raw_analysis():
    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot

    _left, right = _int_pair()
    unsealed = replace(right, raw_parameter_domains=None)
    assert unsealed.to_dict()["raw_parameter_domains"] == "unsealed"
    assert "raw_parameter_domains" not in right.to_dict()
    assert AnalysisSnapshot.from_function_analysis(unsealed).semantic_fingerprint != (
        AnalysisSnapshot.from_function_analysis(right).semantic_fingerprint
    )
