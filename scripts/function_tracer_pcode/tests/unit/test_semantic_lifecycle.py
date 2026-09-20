# -*- coding: utf-8 -*-
"""意味値の一生（Issue #22 PR-22-B, blocker: validated と published の分離）。

確かめるのは 1 点に尽きる:

    「immutable だから solver へ渡してよい」と
    「producer が完成を宣言したから solver へ渡してよい」を混同しない。

identity（candidate hash / 完全比較 / digest）は計算のために graph を検証する
ので、未凍結の入力をその場で凍らせる。そこを公開と同じ 1 bit で表すと、
identity API を 1 回呼んだだけで精錬中の値が solver へ流れ込める。
"""

from __future__ import annotations

import copy
import dataclasses

import pytest

from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.errors import (
    AnalysisFailureError,
    ExpressionCycleError,
    UnpublishedSemanticInputError,
    pair_failure_scope,
)
from scripts.function_tracer_pcode.core.semantic_freeze import (
    publish,
    publish_semantic_values,
)
from scripts.function_tracer_pcode.core.semantic_lifecycle import SemanticLifecycle
from scripts.function_tracer_pcode.core.structural import (
    candidate_hash,
    structural_equals,
    structural_identity_digest,
)


def _sum() -> Expression:
    return Expression.binary_op(
        "INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4)
    )


# ---------------------------------------------------------------------------
# 1. identity は検証まで。公開はしない
# ---------------------------------------------------------------------------


def test_a_new_expression_starts_in_construction():
    expr = _sum()

    assert expr.lifecycle is SemanticLifecycle.CONSTRUCTION
    assert expr.is_frozen is False
    assert expr.is_published is False


@pytest.mark.parametrize(
    "identity_call",
    [
        pytest.param(lambda expr: candidate_hash(expr), id="candidate_hash"),
        pytest.param(lambda expr: structural_identity_digest(expr), id="identity_digest"),
        pytest.param(lambda expr: structural_equals(expr, _sum()), id="structural_equals"),
        pytest.param(lambda expr: expr.freeze(), id="freeze"),
    ],
)
def test_identity_validates_but_never_publishes(identity_call):
    """identity API と `freeze()` は VALIDATED までしか進めない。"""

    expr = _sum()

    identity_call(expr)

    assert expr.is_frozen is True
    assert expr.is_published is False
    assert expr.lifecycle is SemanticLifecycle.VALIDATED


@pytest.mark.parametrize(
    "identity_call",
    [
        pytest.param(lambda expr: candidate_hash(expr), id="candidate_hash"),
        pytest.param(lambda expr: expr.freeze(), id="freeze"),
    ],
)
def test_a_validated_expression_is_still_refused_by_the_solver_renderer(identity_call):
    """凍結済みでも、producer が宣言していなければ solver へ渡せない。"""

    expr = _sum()
    identity_call(expr)

    with pytest.raises(UnpublishedSemanticInputError):
        expr.to_smt()


def test_calling_identity_many_times_does_not_change_the_state():
    expr = _sum()

    for _ in range(5):
        candidate_hash(expr)
        structural_identity_digest(expr)
        expr.freeze()

    assert expr.lifecycle is SemanticLifecycle.VALIDATED


def test_identity_after_publication_does_not_take_the_state_back():
    """遷移は単調。identity を呼んでも公開が取り消されない。"""

    expr = publish(_sum())

    candidate_hash(expr)
    expr.freeze()

    assert expr.lifecycle is SemanticLifecycle.PUBLISHED


# ---------------------------------------------------------------------------
# 2. 公開だけが solver 入力を作る
# ---------------------------------------------------------------------------


def test_publication_makes_the_expression_renderable():
    expr = _sum()

    assert publish(expr) is expr
    assert expr.is_published is True
    assert expr.to_smt() == "(bvadd a (_ bv1 32))"


def test_publication_is_idempotent():
    expr = publish(_sum())
    rendered = expr.to_smt()

    assert publish(expr) is expr
    assert expr.to_smt() == rendered


def test_publication_reaches_every_semantic_descendant():
    left = Expression.parameter("a", 0, size=4)
    right = Expression.constant(1, size=4)
    root = Expression.binary_op("INT_ADD", left, right)

    publish(root)

    assert [child.is_published for child in root.operands] == [True, True]


def test_publication_reaches_phi_branches_and_their_conditions():
    guard = Condition(Expression.parameter("p", 0, size=4))
    taken = Expression.constant(1, size=4)
    other = Expression.constant(2, size=4)
    phi = Expression(
        ExpressionType.PHI,
        value=[(guard, taken), (guard.negate(), other)],
        size=4,
    )

    publish(phi)

    assert phi.is_published is True
    for condition, value in phi.value:
        assert condition.is_published is True, condition.to_string()
        assert condition.expression.is_published is True
        assert value.is_published is True


def test_publication_reaches_expressions_carried_by_a_runtime_ref():
    from scripts.function_tracer_pcode.core.runtime_refs import CountedLoopSummaryRef

    bias = Expression.parameter("bias", 1, size=4)
    ref = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=False,
        residue_cases=((1, 0, 1, 0),),
        residue_bias_terms=((1, 0, bias),),
    )
    expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [
            Expression.constant(0, size=4),
            Expression.parameter("start", 0, size=4),
            Expression.parameter("limit", 2, size=4),
        ],
        size=4,
        runtime_ref=ref,
    )

    publish(expr)

    assert bias.is_published is True


def test_a_condition_follows_the_same_lifecycle():
    condition = Condition(_sum())

    # 構築と同時に検証されるが、公開はされていない。
    assert condition.is_frozen is True
    assert condition.is_published is False
    with pytest.raises(UnpublishedSemanticInputError):
        condition.to_smt()

    publish(condition)

    assert condition.is_published is True
    assert condition.expression.is_published is True
    # 条件は bool へ落として描かれる（式そのものの描画とは別）。
    assert condition.to_smt() == "(not (= (bvadd a (_ bv1 32)) (_ bv0 32)))"


def test_negating_a_published_condition_keeps_the_declaration():
    """条件の反転は「これから仕上げる材料」ではない。

    条件には refinement 段階が無い（構築と同時に凍結される）ので、公開済みの
    条件を反転したものは、producer が宣言し直すものが何も残っていない。
    """

    condition = publish(Condition(_sum()))

    negated = condition.negate()

    assert negated is not condition
    assert negated.is_published is True
    assert negated.to_smt().startswith("(not ") is False or negated.negated is True


def test_negating_an_unpublished_condition_stays_unpublished():
    """公開していない条件を反転しても、公開したことにはならない。"""

    condition = Condition(_sum())

    assert condition.negate().is_published is False


# ---------------------------------------------------------------------------
# 3. 新しい値は宣言を引き継がない
# ---------------------------------------------------------------------------


def test_derive_with_does_not_inherit_publication():
    published = publish(_sum())

    refined = published.derive_with(size=8)

    assert refined is not published
    assert refined.is_published is False
    assert refined.lifecycle is SemanticLifecycle.CONSTRUCTION
    with pytest.raises(UnpublishedSemanticInputError):
        refined.to_smt()


def test_clone_with_does_not_inherit_publication():
    published = publish(_sum())

    assert published.clone_with(size=8).is_published is False


def test_deepcopy_does_not_inherit_publication():
    published = publish(_sum())

    assert copy.deepcopy(published).is_published is False


def test_republishing_a_refined_value_makes_it_usable_again():
    published = publish(_sum())
    refined = published.derive_with(size=8)

    publish(refined)

    assert refined.is_published is True
    assert refined.to_smt()
    # 元の値は別物のまま（精緻化は複製なので元へ波及しない）。
    assert published.size == 4


# ---------------------------------------------------------------------------
# 4. 入れ物からの公開
# ---------------------------------------------------------------------------


@dataclasses.dataclass
class _Carrier:
    """入れ物の形（dataclass）を持つ producer の代役。"""

    value: Expression
    conditions: list
    by_name: dict


def test_publishing_a_carrier_publishes_what_it_reaches():
    value = _sum()
    condition = Condition(Expression.parameter("p", 0, size=4))
    carrier = _Carrier(value=value, conditions=[condition], by_name={"v": value})

    assert publish_semantic_values(carrier) is carrier

    assert value.is_published is True
    assert condition.is_published is True


def test_a_package_carrier_publishes_through_its_own_state():
    """dataclass でない carrier も、`__dict__` 経由で取りこぼさない。

    `ReturnCase` は本番の carrier で、組み立て完了点（`__init__`）で自分から
    公開を宣言する。外から carrier を探して回る層は無い。
    """

    from scripts.function_tracer_pcode.core import ReturnInfo
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase

    value = _sum()
    condition = Condition(Expression.parameter("p", 0, size=4))
    case = ReturnCase(
        index=0,
        conditions=[condition],
        value_expr=value,
        return_info=ReturnInfo(address="0x1", conditions=[], value=value),
    )

    assert case.value_expr.is_published is True
    assert case.conditions[0].is_published is True


def test_a_semantic_value_used_as_a_dict_key_is_published_too():
    """key も意味値になり得る（式を鍵にした cache が実在する）。"""

    key = _sum()
    cache = {key: "whatever"}

    publish_semantic_values({"cache": cache})

    assert key.is_published is True


# ---------------------------------------------------------------------------
# 5. 拒否は PR-106-0 の経路へ乗る
# ---------------------------------------------------------------------------


def test_the_refusal_is_a_typed_internal_failure_recorded_in_the_ledger():
    expr = _sum()
    expr.freeze()

    with pair_failure_scope(("bin1", "bin2"), None) as ledger:
        with pytest.raises(UnpublishedSemanticInputError) as raised:
            expr.to_smt()
        pending = ledger.pending_failure()

    assert isinstance(raised.value, AnalysisFailureError)
    assert pending is not None
    assert pending.is_internal_bug is True
    assert pending.site == "core.render_smt.expression_to_smt"


def test_a_swallowed_refusal_still_leaves_the_ledger_entry():
    expr = _sum()

    with pair_failure_scope(("bin1", "bin2"), None) as ledger:
        try:
            expr.to_smt()
        except Exception:  # 深部の包括捕捉を再現する（test 側の模擬）
            pass
        assert ledger.pending_failure() is not None


# ---------------------------------------------------------------------------
# 6. lifecycle transition は failure-atomic
# ---------------------------------------------------------------------------

_DERIVED_FIELDS = (
    "_snapshot",
    "_local_payload",
    "_structural_hash",
    "_equivalence_digest",
    "_tree_size",
    "_identity_complete",
)


def _cyclic_expression() -> Expression:
    """閉路。`operands` へ直接書いて構築時の検査を通り抜ける。"""

    node = Expression.unary_op("BOOL_NEGATE", Expression.constant(1, 1))
    node.__dict__["operands"] = [node]
    return node


def _root_with_cyclic_runtime_ref():
    """graph 自体は健全で、runtime ref の中だけが閉路になっている root。

    ここが blocker の形: root の graph を先に確定させてから ref を検証すると、
    root だけ VALIDATED で残る。
    """

    from scripts.function_tracer_pcode.core.runtime_refs import CountedLoopSummaryRef

    cyclic = _cyclic_expression()
    ref = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=False,
        residue_cases=((1, 0, 1, 0),),
        residue_bias_terms=((1, 0, cyclic),),
    )
    child = Expression.parameter("start", 0, size=4)
    root = Expression.intrinsic(
        "COUNTED_LOOP_SUM", [Expression.constant(0, size=4), child], size=4,
        runtime_ref=ref,
    )
    return root, child, cyclic


def _assert_nothing_committed(node: Expression) -> None:
    assert node.lifecycle is SemanticLifecycle.CONSTRUCTION, node.lifecycle
    leaked = [name for name in _DERIVED_FIELDS if name in node.__dict__]
    assert leaked == [], leaked


def test_a_cycle_inside_a_runtime_ref_leaves_nothing_validated():
    """closure の一部が失敗したら root も子も確定しない。"""

    root, child, cyclic = _root_with_cyclic_runtime_ref()

    with pytest.raises(ExpressionCycleError):
        root.freeze()

    _assert_nothing_committed(root)
    _assert_nothing_committed(child)
    _assert_nothing_committed(cyclic)


def test_retrying_a_failed_validation_detects_the_cycle_again():
    """失敗後の再試行が、途中で作った派生値を成功結果として拾わない。"""

    root, child, _cyclic = _root_with_cyclic_runtime_ref()

    for _attempt in range(3):
        with pytest.raises(ExpressionCycleError):
            root.freeze()
        _assert_nothing_committed(root)
        _assert_nothing_committed(child)


@pytest.mark.parametrize(
    "identity_call",
    [
        pytest.param(lambda expr: candidate_hash(expr), id="candidate_hash"),
        pytest.param(lambda expr: structural_identity_digest(expr), id="identity_digest"),
    ],
)
def test_identity_apis_re_detect_the_cycle_after_a_failed_validation(identity_call):
    """identity 経由の検証でも同じ contract（1 回目も 2 回目も落ちる）。"""

    root, _child, _cyclic = _root_with_cyclic_runtime_ref()

    with pytest.raises(ExpressionCycleError):
        root.freeze()
    for _attempt in range(2):
        with pytest.raises(ExpressionCycleError):
            identity_call(root)
        _assert_nothing_committed(root)


def test_a_failed_validation_is_recorded_as_an_internal_bug():
    """PR-106-0 の経路は維持（記録してから raise）。"""

    root, _child, _cyclic = _root_with_cyclic_runtime_ref()

    with pair_failure_scope(("bin1", "bin2"), None) as ledger:
        with pytest.raises(ExpressionCycleError):
            root.freeze()
        pending = ledger.pending_failure()

    assert pending is not None
    assert pending.is_internal_bug is True
    assert pending.site == "core.semantic_freeze.freeze_expression"


def test_a_runtime_ref_pointing_back_at_the_root_terminates():
    """back-reference（ref の中の式が root を指す）で無限再帰しない。

    「検証中」を公開 state で表していないので、まだ VALIDATED でない root へ
    戻ってきても止まらなければならない — 止めているのは operation-local な
    staging の方。
    """

    root = Expression.binary_op(
        "INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4)
    )
    # tuple なので `_walk_semantic_carriers` が中を辿る（module 名に依存しない）。
    object.__setattr__(root, "runtime_ref", (root, root.operands[0]))

    assert root.freeze() is root
    assert root.lifecycle is SemanticLifecycle.VALIDATED
    assert root.operands[0].lifecycle is SemanticLifecycle.VALIDATED
    # 2 度目は費用ゼロで、状態も動かない。
    assert root.freeze().lifecycle is SemanticLifecycle.VALIDATED


def test_a_published_value_reached_through_its_own_runtime_ref_terminates():
    """公開でも同じ（back-reference で止まり、closure は published になる）。"""

    root = Expression.binary_op(
        "INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4)
    )
    object.__setattr__(root, "runtime_ref", (root,))

    publish(root)

    assert root.is_published is True
    assert all(child.is_published for child in root.operands)


@pytest.mark.parametrize("healthy_first", [True, False], ids=["healthy_first", "broken_first"])
def test_publication_of_a_carrier_is_all_or_nothing(healthy_first):
    """入れ物の一部が検証できないなら、sibling も solver へ渡せない。

    走査順に依らない性質なので両向きで確かめる。片方の向きでは healthy が
    staging まで進んでから捨てられる（そこが commit されないことが要点）。
    """

    healthy = _sum()
    healthy.freeze()  # 検証は済ませておく（公開だけが失敗する形にする）
    broken = Expression.unary_op("INT_ZEXT", _cyclic_expression())
    values = [healthy, broken] if healthy_first else [broken, healthy]

    with pytest.raises(ExpressionCycleError):
        publish_semantic_values(values)

    assert healthy.is_published is False
    assert healthy.lifecycle is SemanticLifecycle.VALIDATED
    _assert_nothing_committed(broken)


def test_publication_does_not_leave_the_root_published_when_the_closure_fails():
    """root だけ PUBLISHED で残らない（宣言は 1 回の意思表示なので全か無か）。"""

    root, child, _cyclic = _root_with_cyclic_runtime_ref()

    with pytest.raises(ExpressionCycleError):
        publish(root)

    assert root.is_published is False
    assert child.is_published is False
    _assert_nothing_committed(root)


def test_publication_leaves_validation_alone_when_it_fails():
    """検証は別 transaction。公開が失敗しても、検証済みの値は検証済みのまま。

    意味が immutable になったこと自体は事実なので取り消さない。取り消す必要が
    あるのは「producer が宣言した」という主張の側だけ。
    """

    healthy = _sum()
    healthy.freeze()
    broken = Expression.unary_op("INT_ZEXT", _cyclic_expression())
    carrier = _Carrier(value=healthy, conditions=[], by_name={"broken": broken})

    with pytest.raises(ExpressionCycleError):
        publish_semantic_values(carrier)

    assert healthy.lifecycle is SemanticLifecycle.VALIDATED
    assert healthy.is_published is False
