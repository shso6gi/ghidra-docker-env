# -*- coding: utf-8 -*-
"""値・対象の identity が最後の consumer まで保たれること（Issue #218、計画 v4 PR-D、review r4）。

owner（`core.structural`）が厳密な identity を作っても、consumer が自分で digest にして束ねると、digest の
衝突で別の値が 1 つになる。ここでは **process 全体の** `hashlib.sha256` を定数にし（identity の生成だけで
なく、consumer の束ね・bucket・照合・cache の hit まで衝突させる）、production の関数を通して確かめる:

* 同じ identity は共有する（束ねる・同じ bucket・同じ token）
* 違う identity は併合しない
* 識別不能な値は何とも束ねない（確定した判定の根拠にならない）

intern の token は、どの intern が発行したかを含む（別の intern・別の graph の token と等しくならない）。
"""

from __future__ import annotations

import dataclasses
import hashlib

import pytest

from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.runtime_refs import AddressValueRef
from scripts.function_tracer_pcode.core.semantic_freeze import publish
from scripts.function_tracer_pcode.core.structural import object_target_key, value_identity
from scripts.function_tracer_pcode.tests.unit.test_pr_d_value_target_identity import _extend
# 強制衝突の前に読み込む（import 時に自分の登録表の digest を確かめる module がある）
from scripts.function_tracer_pcode.proof.call_effect import obligations as _obligations  # noqa: F401
from scripts.function_tracer_pcode.proof.obligations import guard_overlap as _guard_overlap  # noqa: F401
from scripts.function_tracer_pcode.proof.strategies import pairwise as _pairwise  # noqa: F401
from scripts.function_tracer_pcode.tests.unit import test_call_effect_obligations as _fixtures  # noqa: F401
from scripts.function_tracer_pcode.authority.lifecycle import production_signals as _production_signals  # noqa: F401
from scripts.function_tracer_pcode.authority.decision import conditional as _conditional  # noqa: F401
from scripts.function_tracer_pcode.proof.return_width import pipeline as _return_width_pipeline  # noqa: F401
from scripts.function_tracer_pcode.authority.sites import runtime as _sites_runtime  # noqa: F401
from scripts.function_tracer_pcode.authority.process import operational_extraction as _operational  # noqa: F401


class _ConstantSha:
    """どの入力にも同じ digest を返す `hashlib.sha256` の代わり（強制衝突）。"""

    def __init__(self, data=b""):
        pass

    def update(self, data):
        pass

    def hexdigest(self):
        return "0" * 64

    def digest(self):
        return b"\x00" * 32


@pytest.fixture
def every_sha256_collides(monkeypatch):
    monkeypatch.setattr(hashlib, "sha256", _ConstantSha)
    monkeypatch.setattr(structural, "_TAIL_INTERN", structural._ExactTailIntern())
    monkeypatch.setattr(structural, "_VALIDATED_TAIL_MEMO", structural.WeakKeyedTable())
    yield


# ---------------------------------------------------------------------------
# owner: 厳密な束ね（`dedupe_exact`）と record の intern
# ---------------------------------------------------------------------------


def test_exact_dedupe_shares_equal_values_and_keeps_different_ones_under_a_collision(every_sha256_collides):
    one, two = ("expression", ("const", ("int", 1), 4)), ("expression", ("const", ("int", 2), 4))
    assert structural.dedupe_exact([one, two, one]) == (one, two)
    assert structural.dedupe_exact([("a", 1), ("a", 1)]) == (("a", 1),)


def test_exact_dedupe_keeps_types_apart():
    # 表現が同じ JSON になる別の値（tuple と list・True と 1・"1" と 1）を同じにしない
    assert len(structural.dedupe_exact([(1, 2), [1, 2]])) == 2
    assert len(structural.dedupe_exact([(True,), (1,)])) == 2
    assert len(structural.dedupe_exact([("1",), (1,)])) == 2


def test_an_unidentified_value_is_never_merged():
    class _Opaque:
        pass

    opaque = (_Opaque(),)
    assert len(structural.dedupe_exact([opaque, opaque])) == 2
    token = structural.unidentified_identity("probe")
    assert len(structural.dedupe_exact([("k", token), ("k", token)])) == 2


def test_record_tokens_name_their_intern(every_sha256_collides):
    first, second = structural.ExactRecordIntern(), structural.ExactRecordIntern()
    # 同じ intern: 同じ record は同じ token、別の record は別の token
    assert first.token("d", b"x") == first.token("d", b"x")
    assert first.token("d", b"x") != first.token("d", b"y")
    # 別の intern: 最初に登録した record が違えば（衝突の下で bucket の位置が同じでも）別の token
    assert first.token("d", b"p") != second.token("d", b"q")
    # 同じ record でも別の intern の token は別（intern の外で比べない）
    assert first.token("d", b"x") != second.token("d", b"x")


def test_two_fresh_interns_with_one_record_each_never_share_a_token(every_sha256_collides):
    # 最小の反例（review r4 m1）: 別々の intern に別の record を 1 つずつ。印が無いと両方とも
    # (tag, digest, 0) になる
    assert structural.ExactRecordIntern().token("d", b"p") != structural.ExactRecordIntern().token("d", b"q")


def test_a_copied_intern_is_the_same_intern():
    import copy

    intern = structural.ExactRecordIntern()
    token = intern.token("d", b"x")
    assert copy.deepcopy(intern) is intern and copy.copy(intern) is intern
    assert copy.deepcopy(intern).token("d", b"x") == token


def test_occurrence_identity_merges_copies_of_one_token_but_value_identity_does_not():
    token = structural.unidentified_identity("probe")
    assert structural.exact_occurrence_key(("k", token)) == structural.exact_occurrence_key(("k", token))
    assert structural.exact_value_key(("k", token)) != structural.exact_value_key(("k", token))
    assert structural.exact_occurrence_key((1, 2)) != structural.exact_occurrence_key([1, 2])


def _guard_case(conditions_smt):
    from types import SimpleNamespace

    return SimpleNamespace(index=0, conditions=(), get_conditions_smt=lambda renderer: list(conditions_smt))


def test_guard_requirements_of_two_graphs_never_coincide(every_sha256_collides):
    from scripts.function_tracer_pcode.proof.obligations import guard_overlap

    left = guard_overlap.guard_seed("left", _guard_case(["(a)"]), None)
    right = guard_overlap.guard_seed("right", _guard_case(["(b)"]), None)
    first = guard_overlap.GuardOverlapGraph(("view",), "premise")
    second = guard_overlap.GuardOverlapGraph(("view",), "premise")
    one = first.requirement(left, right, "(assert x)\n(check-sat)")
    other = second.requirement(left, right, "(assert y)\n(check-sat)")
    assert one.canonical_query_digest == other.canonical_query_digest
    assert one.stable_key() != other.stable_key()
    # 同じ graph の同じ query は同じ node
    assert first.requirement(left, right, "(assert x)\n(check-sat)").stable_key() == one.stable_key()
    # 別の graph の node は引けない
    assert second.lookup(one) is None


# ---------------------------------------------------------------------------
# consumer: call effect の抽出（`_extract_side_facts`）
# ---------------------------------------------------------------------------


def _analysis(call_arguments, summary_arguments):
    """1 つ以上の call を持つ解析（引数の証拠と callee の要約の証拠）。"""

    from scripts.function_tracer_pcode.tests.unit.test_call_effect_obligations import _analysis_with_call, _pcode_ref

    analysis = _analysis_with_call("left", 0x1000, 0x1010, 0x2000)
    summary = analysis.effect_summary
    (key, evidence), = summary.call_argument_evidence.items()
    site, = summary.call_site_effect_summary_evidence
    argument_evidence = {}
    sites = []
    for index, (call_argument, summary_argument) in enumerate(zip(call_arguments, summary_arguments)):
        pcode_ref = evidence.pcode_op_ref if index == 0 else _pcode_ref("left", 0x1000, 0x1010 + 0x10 * index)
        argument_evidence[pcode_ref.stable_key()] = dataclasses.replace(
            evidence, pcode_op_ref=pcode_ref, arguments=(call_argument,),
        )
        sites.append(dataclasses.replace(
            site,
            pcode_op_ref=pcode_ref,
            argument_keys=(value_identity(summary_argument),),
            argument_target_keys=(object_target_key(summary_argument),),
            return_value_keys=(value_identity(summary_argument),),
            return_value_target_keys=(object_target_key(summary_argument),),
            return_partitions=(((), summary_argument),),
        ))
    summary.call_argument_evidence.clear()
    summary.call_argument_evidence.update(argument_evidence)
    summary.call_site_effect_summary_evidence = tuple(sites)
    return analysis


def _call_site_facts(analysis):
    from scripts.function_tracer_pcode.proof.call_effect.obligations import CallSiteFact, _extract_side_facts

    return [fact for fact in _extract_side_facts(analysis, binary_name="left") if type(fact) is CallSiteFact]


def test_two_evidence_values_with_one_target_stay_ambiguous_under_a_collision(every_sha256_collides):
    # 同じ対象の ZEXT(p) と SEXT(p) を 1 つの call の 2 つの証拠が渡す。digest が衝突しても 1 つに束ねない
    fact, = _call_site_facts(_analysis([publish(_extend("INT_ZEXT"))], [publish(_extend("INT_SEXT"))]))
    assert "argument_groups_ambiguous" in fact.extraction_failure_causes
    assert fact.extraction_status != "complete"
    assert fact.argument_keys == ()


def test_the_same_value_from_two_evidences_is_still_one_argument_group(every_sha256_collides):
    value = publish(_extend("INT_ZEXT"))
    fact, = _call_site_facts(_analysis([value], [publish(_extend("INT_ZEXT"))]))
    assert "argument_groups_ambiguous" not in fact.extraction_failure_causes
    assert fact.argument_keys == (value_identity(value),)


def test_two_calls_keep_their_own_buckets_under_a_collision(every_sha256_collides):
    # 別々の call（P-code op の key が違う）の証拠は、bucket の digest が衝突しても混ざらない
    address = publish(Expression(
        ExpressionType.CONSTANT, value=0x100064, size=8,
        runtime_ref=AddressValueRef(address_offset=0x100064, program_id=1, space_name="ram"),
    ))
    zext = publish(_extend("INT_ZEXT"))
    facts = _call_site_facts(_analysis([address, zext], [address, zext]))
    assert len(facts) == 2
    assert sorted(len(fact.argument_keys) for fact in facts) == [1, 1]
    assert all("argument_groups_ambiguous" not in fact.extraction_failure_causes for fact in facts)


def test_the_pcode_census_compares_op_keys_exactly(every_sha256_collides):
    # 構造の被覆の census: P-code の op の集合と fact の op の集合を digest の一致で同じとしない
    from scripts.function_tracer_pcode.proof.call_effect.obligations import _structural_coverage_failure_causes

    payload = {"structural_coverage_complete": True}
    for side in ("left", "right"):
        payload[f"{side}_census_status"] = "complete"
        payload[f"{side}_census_pcode_op_keys"] = [["pcode_op", 1, 0x10]]
        payload[f"{side}_fact_pcode_op_keys"] = [["pcode_op", 1, 0x10]]
    assert "left_pcode_census_fact_key_mismatch" not in _structural_coverage_failure_causes(payload)
    payload["left_fact_pcode_op_keys"] = [["pcode_op", 1, 0x20]]
    assert "left_pcode_census_fact_key_mismatch" in _structural_coverage_failure_causes(payload)


def test_a_token_inside_an_early_return_branch_never_matches_across_sides():
    # 左右の部品 key の分岐（parameter の atom など）が子の一部だけを返しても、その中の process の中だけの
    # token は左右の一致に使わない
    from scripts.function_tracer_pcode.core.semantic_projection import canonical_atom
    from scripts.function_tracer_pcode.proof.call_effect.obligations import _cross_binary_expression_shape
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    token = structural.exact_tail_token(Expression.parameter("deep", 0, "int", size=4))
    wrapped = canonical_atom(("parameter", 1, 0x100, token))
    component = PairwiseStrategy._cross_binary_call_effect_component_key
    assert component(("argument", wrapped)) != component(("argument", wrapped))
    assert _cross_binary_expression_shape(("runtime_ref", wrapped)) != _cross_binary_expression_shape(("runtime_ref", wrapped))
    # 対照: token の無い parameter の atom は左右で同じ形
    plain = canonical_atom(("parameter", 1, 0x100, 2))
    assert component(("argument", plain)) == component(("argument", canonical_atom(("parameter", 2, 0x200, 2))))


def test_prerequisite_signals_with_different_targets_survive_a_collision(every_sha256_collides):
    from types import SimpleNamespace

    from scripts.function_tracer_pcode.authority.domains.call_effect import _dedupe_prerequisite_signals

    def signal(target):
        return SimpleNamespace(reason_id="r", canonical_target_key=target, missing_semantic_fact="m")

    zext = ("target", value_identity(publish(_extend("INT_ZEXT"))))
    sext = ("target", value_identity(publish(_extend("INT_SEXT"))))
    kept = _dedupe_prerequisite_signals([signal(zext), signal(sext), signal(zext)])
    assert [item.canonical_target_key for item in kept].count(zext) == 1
    assert len(kept) == 2


def test_the_shared_z3_session_checks_each_region_formula_as_itself(monkeypatch):
    # 共有の Z3 session は region の formula を formula の文字列で引く: digest が衝突した 2 つの region
    # の一方の assertion で、もう一方を解かない
    from types import SimpleNamespace

    from scripts.function_tracer_pcode.proof import monolithic_authority
    from scripts.function_tracer_pcode.smt.interface import SolverStatus

    prelude = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n"
    unsat = prelude + "(assert (= x #x01))\n(assert (= x #x02))\n(check-sat)\n"
    sat = prelude + "(assert (= x #x01))\n(check-sat)\n"
    real = hashlib.sha256

    def colliding(data=b""):
        if isinstance(data, bytes) and data.startswith(b"(set-logic QF_BV)\n(declare-const x"):
            return _ConstantSha(data)
        return real(data)

    monkeypatch.setattr(monolithic_authority, "hashlib", SimpleNamespace(sha256=colliding))
    queries = tuple(
        SimpleNamespace(formula=formula, contract=SimpleNamespace(formula_digest="0" * 64))
        for formula in (unsat, sat)
    )
    session = monolithic_authority.SharedZ3RegionSession(
        SimpleNamespace(queries=queries, query_set_digest="set"), SimpleNamespace(execution_lease_digest="lease"),
    )
    assert session.execute(unsat, 5000).results[0].status is SolverStatus.UNSAT
    assert session.execute(sat, 5000).results[0].status is SolverStatus.SAT



class _Signal:
    def __init__(self, target):
        self.target_value = target

    def _phase7_signal_authority(self):
        return {"reason_id": "r", "target": self.target_value}


def _pilot_session(emitted):
    from types import SimpleNamespace

    return SimpleNamespace(
        domain_signal_encoder=SimpleNamespace(accepts_signal_type=lambda kind: True),
        domain_signal_state={}, phase7_runtime=None,
        emit_domain_signal=lambda signal: emitted.append(signal) or 1,
    )


def test_each_distinct_call_effect_signal_is_emitted_under_a_collision(every_sha256_collides, monkeypatch):
    # 1 回だけ出す signal の集合: digest が衝突した別の target の signal を捨てない（blocker を落とさない）
    emitted = []
    session = _pilot_session(emitted)
    monkeypatch.setattr(_production_signals, "active_production_pilot_session", lambda: session)
    zext = _Signal(value_identity(publish(_extend("INT_ZEXT"))))
    sext = _Signal(value_identity(publish(_extend("INT_SEXT"))))
    site = "pr-d-test-site"
    for signal in (zext, sext, zext):
        _production_signals.emit_call_effect_signal(signal, producer_site_manifest_id=site)
    assert emitted == [zext, sext]


def test_each_distinct_return_width_signal_is_emitted_under_a_collision(every_sha256_collides, monkeypatch):
    emitted = []
    session = _pilot_session(emitted)
    monkeypatch.setattr(_production_signals, "active_production_pilot_session", lambda: session)
    monkeypatch.setattr(
        _production_signals, "emit_abi_width_readonly_signal",
        lambda signal, producer_site_manifest_id=None: emitted.append(signal) or 1,
    )
    one, two = _Signal(("a",)), _Signal(("b",))
    for signal in (one, two, one):
        _return_width_pipeline._emit_return_width_signal_once(signal, producer_site_manifest_id="pr-d-site")
    assert emitted == [one, two]


def test_distinct_assumption_premises_survive_a_collision(every_sha256_collides):
    from scripts.function_tracer_pcode.proof.assumptions import AssumptionKind, AssumptionPremise

    def premise(subject):
        return AssumptionPremise(
            kind=AssumptionKind.EXTERNAL_CALLEE_SPEC, subject=subject,
            payload={"canonical_symbol": subject, "signature": ("double", "double"),
                     "no_observable_memory_write": True, "returns_normally": True},
        )

    kept = _conditional.canonical_assumption_dependencies([premise("log"), premise("exp"), premise("log")])
    assert sorted(item.subject for item in kept) == ["exp", "log"]



def test_the_authority_identity_keeps_apart_what_the_digest_preimage_merges():
    # `authority_digest` の preimage（canonical_value の JSON）は型を落とす。identity は落とさない
    import enum

    from scripts.function_tracer_pcode.authority.contracts import (
        authority_digest, authority_identity_key, canonical_value,
    )

    class _Kind(enum.Enum):
        ONE = "one"

    @dataclasses.dataclass(frozen=True)
    class _A:
        x: int

    @dataclasses.dataclass(frozen=True)
    class _B:
        x: int

    pairs = [
        ({"a": 1}, (("a", 1),)),
        ({1: "v"}, {"1": "v"}),
        (_Kind.ONE, "one"),
        (_A(1), _B(1)),
        (frozenset({1}), (1,)),
        (True, 1),
    ]
    for left, right in pairs:
        if not isinstance(left, bool):
            assert authority_digest(left) == authority_digest(right), (left, right)
        assert authority_identity_key(left) != authority_identity_key(right), (left, right)
        assert authority_identity_key(left) == authority_identity_key(left)
    assert canonical_value({"a": 1}) == canonical_value((("a", 1),))
    # authority の不変の形（`freeze_authority_value`）で同じ値は同じ identity（list と tuple）。dataclass の
    # field の中でも同じ
    assert authority_identity_key([1, (2, [3])]) == authority_identity_key((1, (2, (3,))))
    assert authority_identity_key(_A([1])) == authority_identity_key(_A((1,)))

    class _Spec(dict):
        """容器の subclass でも `to_authority_dict` で読む。"""

        def __init__(self, contents, authority):
            super().__init__(contents)
            self.authority = authority

        def to_authority_dict(self):
            return {"spec": self.authority}

    assert authority_identity_key(_Spec({"k": 1}, "a")) != authority_identity_key(_Spec({"k": 1}, "b"))
    assert authority_digest(_Spec({"k": 1}, "a")) != authority_digest(_Spec({"k": 1}, "b"))


def test_readonly_value_symbols_are_never_shared_for_an_unidentified_key():
    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import _readonly_value_symbol_key

    body = ("side_local_readonly_value_v2", "left", ("parameter", 0), 4, 0, 0, "d")
    assert _readonly_value_symbol_key(body, 0) == _readonly_value_symbol_key(body, 1)
    token = structural.unidentified_identity("probe")
    unidentified = body[:-1] + (token,)
    assert _readonly_value_symbol_key(unidentified, 0) != _readonly_value_symbol_key(unidentified, 1)
    # 記号は左右で共有する: process の中だけの token（exact tail）を含む key も共有しない
    tail = structural.exact_tail_token(Expression.parameter("p", 0, "int", size=4))
    side_local = body[:-1] + (tail,)
    assert _readonly_value_symbol_key(side_local, 0) != _readonly_value_symbol_key(side_local, 1)


def test_signals_that_differ_only_in_type_are_both_emitted(monkeypatch):
    # 1 回だけ出す集合は型を落とさない: digest の preimage が同じでも別の signal なら出す
    import enum

    class _Kind(enum.Enum):
        ONE = "one"

    emitted = []
    session = _pilot_session(emitted)
    monkeypatch.setattr(_production_signals, "active_production_pilot_session", lambda: session)
    by_enum, by_value = _Signal(_Kind.ONE), _Signal("one")
    for signal in (by_enum, by_value, by_enum):
        _production_signals.emit_call_effect_signal(signal, producer_site_manifest_id="pr-d-site")
    assert emitted == [by_enum, by_value]


class _TargetRef:
    """`stable_key()` だけを持つ call target（list と tuple の違いだけがある 2 つを作る）。"""

    def __init__(self, key):
        self.key = key

    def stable_key(self):
        return self.key


def test_call_targets_that_a_json_projection_merges_stay_two_candidates():
    # 束ねは型まで比べる: JSON（`_jsonable`）にすると同じになる 2 つの target を 1 つにしない
    # （digest の衝突が無くても、JSON の文字列で束ねる実装に戻すとここで落ちる）
    analysis = _analysis([publish(_extend("INT_ZEXT"))], [publish(_extend("INT_ZEXT"))])
    summary = analysis.effect_summary
    (key, evidence), = summary.call_argument_evidence.items()
    summary.call_argument_evidence[key] = dataclasses.replace(
        evidence, target_ref=_TargetRef(("function", 1, [0x2000])),
    )
    site, = summary.call_site_effect_summary_evidence
    summary.call_site_effect_summary_evidence = (
        dataclasses.replace(site, target_ref=_TargetRef(("function", 1, (0x2000,)))),
    )
    fact, = _call_site_facts(analysis)
    assert len(fact.target_candidates) == 2
    assert fact.target_resolution_status == "ambiguous"
