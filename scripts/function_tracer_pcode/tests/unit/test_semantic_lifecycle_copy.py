# -*- coding: utf-8 -*-
"""複製・派生と lifecycle（Issue #22 PR-22-B, blocker: copy 後の PUBLISHED closure）。

確かめるのは 2 点:

1. **複製・派生は公開の権限を持たない**。`copy` / `deepcopy` / `clone_with` /
   `derive_with` から出てきた値は、元が公開済みでも CONSTRUCTION から始まる。
   唯一の例外が `Condition.negate()`（式 object をそのまま持つので closure が
   壊れない）で、表の中でもその 1 行だけが違って見えるようにしてある。
2. **PUBLISHED な値から未公開の意味値へ到達できない**（closure invariant）。
   外側の条件だけが公開済みで中の式が未公開、という形を作れないこと。

2 が壊れると判定面に出る: 公開走査は公開済みの条件で早期 return して式へ降り
ないので、**公開漏れを公開そのものが隠す**。solver renderer は外側の条件しか
見ないため、未公開の式がそのまま SMT になる。
"""

from __future__ import annotations

import copy

import pytest

from scripts.function_tracer_pcode.core import Condition, Expression
from scripts.function_tracer_pcode.core.analysis import ReturnInfo
from scripts.function_tracer_pcode.core.errors import UnpublishedSemanticInputError
from scripts.function_tracer_pcode.core.semantic_freeze import (
    publish,
    unpublished_semantic_values,
)
from scripts.function_tracer_pcode.core.semantic_lifecycle import SemanticLifecycle
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase


CONSTRUCTION = SemanticLifecycle.CONSTRUCTION
VALIDATED = SemanticLifecycle.VALIDATED
PUBLISHED = SemanticLifecycle.PUBLISHED


def _sum(name: str = "a") -> Expression:
    return Expression.binary_op(
        "INT_ADD",
        Expression.parameter(name, 0, size=4),
        Expression.constant(1, size=4),
    )


def _guard(name: str = "a") -> Expression:
    return Expression.binary_op(
        "INT_LESS", Expression.parameter(name, 0, size=4), Expression.constant(7, size=4)
    )


def _expression_in(state: SemanticLifecycle) -> Expression:
    expr = _sum()
    if state >= VALIDATED:
        expr.freeze()
    if state is PUBLISHED:
        publish(expr)
    assert expr.lifecycle is state
    return expr


def _condition_in(state: SemanticLifecycle) -> Condition:
    condition = Condition(_guard())
    if state is PUBLISHED:
        publish(condition)
    assert condition.lifecycle is state
    return condition


# ---------------------------------------------------------------------------
# 1. blocker: 公開済みの条件を deepcopy しても宣言は付いてこない
# ---------------------------------------------------------------------------


def test_deepcopying_a_published_condition_declares_nothing_and_can_be_republished():
    """指摘の筋書きをそのまま辿る（複製 → 拒否 → 公開 → 通る）。"""

    condition = publish(Condition(_guard()))
    assert condition.is_published and condition.expression.is_published

    copied = copy.deepcopy(condition)

    # 複製は宣言を名乗らない。
    assert copied.is_published is False
    assert copied.expression.is_published is False
    # 条件は構築と同じ道を通るので、検証までは済んでいる。
    assert copied.lifecycle is VALIDATED
    # solver 入口は未公開の入力を拒否する。
    with pytest.raises(UnpublishedSemanticInputError):
        copied.to_smt()

    publish(copied)

    # 宣言し直すと closure ごと公開される。
    assert copied.is_published and copied.expression.is_published
    assert unpublished_semantic_values(copied) == ()
    assert copied.to_smt()


def test_a_deepcopied_condition_does_not_share_the_original_expression():
    condition = publish(Condition(_guard()))

    copied = copy.deepcopy(condition)

    assert copied.expression is not condition.expression
    # 元の宣言は複製に触られない。
    assert condition.is_published and condition.expression.is_published


def test_publishing_a_deepcopied_condition_leaves_the_original_alone():
    condition = Condition(_guard())
    copied = copy.deepcopy(condition)

    publish(copied)

    assert copied.is_published is True
    assert condition.is_published is False


def test_a_shallow_copy_of_a_condition_shares_the_expression_but_not_the_declaration():
    condition = publish(Condition(_guard()))

    copied = copy.copy(condition)

    assert copied is not condition
    assert copied.expression is condition.expression
    assert copied.is_published is False
    assert copied.lifecycle is VALIDATED


def test_the_same_condition_reached_twice_is_copied_once():
    """memo を共有するので、carrier の中で同じ条件が 2 度現れても複製は 1 つ。"""

    condition = publish(Condition(_guard()))
    carrier = {"left": condition, "right": condition}

    copied = copy.deepcopy(carrier)

    assert copied["left"] is copied["right"]
    assert copied["left"] is not condition


# ---------------------------------------------------------------------------
# 2. lifecycle × 操作の表（将来 state を足したときに規則が崩れないように）
# ---------------------------------------------------------------------------

#: 値を作り直す操作 = 複製・派生。**どの開始状態からでも CONSTRUCTION**。
_EXPRESSION_DERIVATIONS = (
    ("copy", lambda expr: copy.copy(expr)),
    ("deepcopy", lambda expr: copy.deepcopy(expr)),
    ("clone_with", lambda expr: expr.clone_with(size=8)),
    ("derive_with", lambda expr: expr.derive_with(size=8)),
)


@pytest.mark.parametrize("start", [CONSTRUCTION, VALIDATED, PUBLISHED])
@pytest.mark.parametrize("label,derive", _EXPRESSION_DERIVATIONS, ids=[n for n, _ in _EXPRESSION_DERIVATIONS])
def test_an_expression_derivation_starts_a_new_value_in_construction(label, derive, start):
    expr = _expression_in(start)

    derived = derive(expr)

    assert derived is not expr
    assert derived.lifecycle is CONSTRUCTION, label
    # 元の値は動かない（派生は元の宣言を取り消しも進めもしない）。
    assert expr.lifecycle is start


@pytest.mark.parametrize("start", [CONSTRUCTION, VALIDATED, PUBLISHED])
@pytest.mark.parametrize("label,derive", _EXPRESSION_DERIVATIONS, ids=[n for n, _ in _EXPRESSION_DERIVATIONS])
def test_an_expression_derivation_keeps_no_derived_identity(label, derive, start):
    """状態と一緒に、検証で確定した snapshot / hash / digest も落ちる。"""

    derived = derive(_expression_in(start))

    assert derived.structural_hash() is None, label
    assert derived.tree_size() is None, label
    assert derived.__dict__.get("_snapshot") is None, label
    assert derived.__dict__.get("_equivalence_digest") is None, label


@pytest.mark.parametrize("start", [CONSTRUCTION, VALIDATED, PUBLISHED])
def test_a_shallow_copy_shares_the_children_but_owns_its_operand_list(start):
    """浅い複製は子を共有し、root だけ独立している。

    `operands` を入れ直さないと、検証済みの式を浅く複製したときに
    「CONSTRUCTION なのに `operands` が tuple」という、仕上げられない値ができる。
    """

    expr = _expression_in(start)

    clone = copy.copy(expr)

    # 子は同じ object（浅い複製なので）。
    assert list(clone.operands) == list(expr.operands)
    for cloned_child, child in zip(clone.operands, expr.operands):
        assert cloned_child is child
    # 入れ物は複製のもの。仕上げられる形で始まる。
    assert isinstance(clone.operands, list)
    clone.operands.append(Expression.constant(9, size=4))
    assert len(expr.operands) == 2


_CONDITION_DERIVATIONS = (
    # (label, 操作, 元が VALIDATED のときの結果, 元が PUBLISHED のときの結果)
    ("copy", lambda cond: copy.copy(cond), VALIDATED, VALIDATED),
    ("deepcopy", lambda cond: copy.deepcopy(cond), VALIDATED, VALIDATED),
    # negate だけが宣言を引き継ぐ。式 object をそのまま持つので closure が壊れない。
    ("negate", lambda cond: cond.negate(), VALIDATED, PUBLISHED),
)


@pytest.mark.parametrize("start", [VALIDATED, PUBLISHED])
@pytest.mark.parametrize(
    "label,derive,from_validated,from_published",
    _CONDITION_DERIVATIONS,
    ids=[row[0] for row in _CONDITION_DERIVATIONS],
)
def test_a_condition_derivation_follows_the_owner_contract(
    label, derive, from_validated, from_published, start
):
    condition = _condition_in(start)

    derived = derive(condition)

    expected = from_validated if start is VALIDATED else from_published
    assert derived is not condition
    assert derived.lifecycle is expected, label
    assert condition.lifecycle is start
    # 宣言を引き継いだ場合は closure も引き継いでいること。
    if derived.lifecycle is PUBLISHED:
        assert unpublished_semantic_values(derived) == ()


def test_a_condition_is_validated_the_moment_it_is_built():
    """条件には CONSTRUCTION に留まる時間が無い（表の出発点）。"""

    assert Condition(_guard()).lifecycle is VALIDATED


# ---------------------------------------------------------------------------
# 3. closure invariant
# ---------------------------------------------------------------------------


def _phi_with_branch_condition() -> Expression:
    condition = Condition(_guard())
    return Expression.phi([(condition, _sum()), (condition.negate(), _sum("b"))])


@pytest.mark.parametrize(
    "build",
    [_sum, _guard, _phi_with_branch_condition],
    ids=["binary_op", "comparison", "phi_with_branch_conditions"],
)
def test_a_published_value_has_no_unpublished_semantic_descendant(build):
    value = publish(build())

    assert value.is_published is True
    assert unpublished_semantic_values(value) == ()


def test_the_closure_query_finds_what_publication_would_have_missed():
    """不変条件の検査が空振りしていないこと（壊れた closure を組み立てて見せる）。

    既定の deepcopy がやっていたのと同じ形——公開済みの条件の下に未公開の式——
    を手で作り、query がそれを見つけることを確かめる。
    """

    condition = publish(Condition(_guard()))
    broken = copy.deepcopy(condition)
    broken.__dict__["_published"] = True  # 既定 deepcopy が写していた 1 bit

    found = unpublished_semantic_values(broken)

    assert broken.is_published is True
    # 外側は（嘘だが）公開済みを名乗っているので、そこで止まると何も見つからない。
    assert broken not in found
    # query は条件を通り抜けて式とその子まで降りる。
    assert broken.expression in found
    assert set(found) == {broken.expression, *broken.expression.operands}


def test_publishing_a_broken_closure_again_repairs_it():
    """外側が公開済みでも、`publish` を通せば closure は閉じる。"""

    broken = copy.deepcopy(publish(Condition(_guard())))
    broken.__dict__["_published"] = True

    publish(broken.expression)

    assert unpublished_semantic_values(broken) == ()


# ---------------------------------------------------------------------------
# 4. production の carrier 経路（`proof/strategies/loop_template.py` と同じ形）
# ---------------------------------------------------------------------------


def _return_case(index: int = 0) -> ReturnCase:
    condition = Condition(_guard())
    value = _sum()
    return ReturnCase(
        index=index,
        conditions=[condition, condition.negate()],
        value_expr=value,
        return_info=ReturnInfo(address="0x1000", value=value, conditions=[condition]),
        normalized_value_expr=_sum("n"),
        return_type="int",
    )


def test_a_return_case_publishes_the_closure_it_carries():
    case = _return_case()

    assert unpublished_semantic_values(case) == ()


def test_deepcopying_a_return_case_declares_nothing_until_the_producer_says_so():
    """`deepcopy(case)` の直後は、複製の中身がまだ誰にも宣言されていない。"""

    case = _return_case()

    template = copy.deepcopy(case)

    assert unpublished_semantic_values(template) != ()
    # 旧実装ではここで条件だけが公開済みに見え、式が置き去りになっていた。
    for condition in template.conditions:
        assert condition.is_published is False


def test_the_loop_template_path_publishes_every_solver_consumed_value():
    """`deepcopy(case)` → `replace_value(...)` → 公開、という production の順序。"""

    case = _return_case()
    template = copy.deepcopy(case)

    template.replace_value(_sum("t"), normalized_value_expr=_sum("tn"))

    assert unpublished_semantic_values(template) == ()
    assert template.value_expr.is_published is True
    assert template.normalized_value_expr.is_published is True
    for condition in template.conditions:
        assert condition.is_published is True
        assert condition.expression.is_published is True
    for condition in template.summary_conditions:
        assert condition.is_published is True
        assert condition.expression.is_published is True
    # solver 入口まで届くこと（拒否されない）。
    assert template.get_conditions_smt(None)


def test_updating_the_conditions_of_a_copied_case_publishes_them_too():
    template = copy.deepcopy(_return_case())

    template.update_conditions([Condition(_guard("c"))])

    assert unpublished_semantic_values(template) == ()
