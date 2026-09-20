# -*- coding: utf-8 -*-
"""凍結境界の契約（Issue #22 PR-22-B、計画 B1 / B7 / B10 / B13）。

construction → freeze → immutable consumption の 3 段階がそれぞれ何を許し何を
拒むかを固定する。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.errors import FrozenExpressionError
from scripts.function_tracer_pcode.core.expression import (
    Expression,
    ExpressionType,
    PhiBranch,
)
from scripts.function_tracer_pcode.core.semantic_snapshot import (
    canonical_value_key,
    semantic_projection,
    value_key_is_opaque,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo


def _phi_expression():
    left = Expression.parameter("a", 0, size=4)
    right = Expression.parameter("b", 1, size=4)
    guard = Condition(Expression.binary_op("INT_LESS", left, right))
    inner = Expression.phi([(guard, left), (None, right)])
    outer = Expression.phi([(guard, inner), (None, left)])
    return outer, guard, left, right, inner


# ---------------------------------------------------------------------------
# B1: 凍結前は構築できる / 凍結後は意味 field を書き換えられない
# ---------------------------------------------------------------------------


def test_construction_before_freeze_can_still_set_semantic_fields():
    expr = Expression.binary_op("INT_ADD", Expression.constant(1, 4), Expression.constant(2, 4))
    expr.size = 8
    expr.name = "built"
    assert expr.is_frozen is False
    assert expr.size == 8


@pytest.mark.parametrize(
    "field, value",
    [
        ("size", 8),
        ("name", "renamed"),
        ("operands", ()),
        ("value", 7),
        ("operator", "INT_SUB"),
        ("runtime_ref", object()),
        ("storage_info", StorageInfo(is_register=True, register_name="r1")),
        ("data_type_obj", object()),
        ("read_order_key", 3),
        ("opcode", 11),
        ("_recurrence_semantic_key", ("k",)),
    ],
)
def test_frozen_expression_rejects_semantic_field_writes(field, value):
    expr = Expression.binary_op("INT_ADD", Expression.constant(1, 4), Expression.constant(2, 4))
    expr.freeze()
    with pytest.raises(FrozenExpressionError):
        setattr(expr, field, value)


def test_frozen_phi_branches_and_nested_values_are_immutable():
    outer, guard, left, _right, inner = _phi_expression()
    outer.freeze()

    assert isinstance(outer.value, tuple)
    assert all(isinstance(branch, PhiBranch) for branch in outer.value)
    assert inner.is_frozen and left.is_frozen and guard.is_frozen

    with pytest.raises(FrozenExpressionError):
        outer.value = ()
    with pytest.raises(FrozenExpressionError):
        inner.size = 99
    with pytest.raises(FrozenExpressionError):
        guard.expression = left
    with pytest.raises(FrozenExpressionError):
        guard.negated = True
    with pytest.raises(FrozenExpressionError):
        outer.value[0].value.size = 99
    with pytest.raises(AttributeError):
        # PhiBranch は NamedTuple なので要素の差し替え自体ができない。
        outer.value[0].value = left


def test_condition_is_frozen_on_construction():
    expr = Expression.parameter("a", 0, size=4)
    condition = Condition(expr)
    assert condition.is_frozen is True
    assert expr.is_frozen is True
    with pytest.raises(FrozenExpressionError):
        condition.negated = True


def test_negate_returns_a_new_condition_and_leaves_the_original():
    condition = Condition(Expression.parameter("a", 0, size=4))
    negated = condition.negate()
    assert negated is not condition
    assert condition.negated is False
    assert negated.negated is True


def test_clone_with_does_not_inherit_freeze_and_carries_the_recurrence_key():
    expr = Expression(
        ExpressionType.VARIABLE,
        name="v",
        size=4,
        recurrence_semantic_key=("recurrence", "k0"),
    )
    expr.freeze()
    assert expr.semantic_key() == ("recurrence", "k0")

    clone = expr.clone_with(size=8)
    assert clone.is_frozen is False
    assert clone.size == 8
    assert clone.semantic_key() == ("recurrence", "k0")
    # 元の式は動かない。
    assert expr.size == 4
    clone.size = 16  # 未凍結なので構築の続きができる
    assert clone.size == 16


def test_deepcopy_thaws_the_copy_without_touching_the_source():
    from copy import deepcopy

    expr = Expression.binary_op("INT_ADD", Expression.constant(1, 4), Expression.parameter("a", 0))
    expr.freeze()
    clone = deepcopy(expr)
    assert clone.is_frozen is False
    clone.size = 16
    assert expr.size != 16


# ---------------------------------------------------------------------------
# B7: 凍結済みの入力を受ける「既存 object の書き換え」site が壊れない
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("freeze_first", [False, True])
def test_derive_with_always_returns_a_new_expression(freeze_first):
    """凍結の有無で振る舞いを変えない。未凍結でも元の式は動かない。"""

    expr = Expression.parameter("a", 0, size=0)
    if freeze_first:
        expr.freeze()
    updated = expr.derive_with(size=4)
    assert updated is not expr
    assert updated.size == 4
    assert expr.size == 0
    assert updated.is_frozen is False


def test_two_owners_of_an_unfrozen_expression_do_not_see_each_others_width():
    """共有された未凍結の式に、片方の文脈の幅が漏れない。

    展開値や trace cache は同じ式 object を複数の文脈から指すことがある。
    「まだ凍っていないから書き換えてよい」にすると、この漏れが起きる。
    """

    shared = Expression.parameter("a", 0, size=0)
    owner_a_value = shared
    owner_b_value = shared

    owner_a_value = owner_a_value.derive_with(size=4)

    assert owner_a_value.size == 4
    assert owner_b_value.size == 0
    assert shared.size == 0
    assert owner_a_value is not shared


def test_a_shared_expansion_value_is_not_resized_for_other_consumers():
    """実際の site（展開値の幅合わせ）でも共有元が動かないこと。"""

    from scripts.function_tracer_pcode.semantics.transform.expander_support import (
        ExpandedValue,
        resized_expanded_values,
    )

    shared = Expression.parameter("a", 0, size=0)
    values = [ExpandedValue(shared, []), ExpandedValue(shared, [])]
    resized = resized_expanded_values(values, 4)

    assert [item.value.size for item in resized] == [4, 4]
    assert shared.size == 0, "the shared expression must not be widened in place"


MUTATION_SITES = [
    ("semantics.transform.expander", "_coerce_value_to_output_size"),
    ("semantics.transform.expander", "_expand_input_varnode"),
    ("semantics.transform.expander", "_trace_operation_expression"),
    ("semantics.transform.expander", "_expand_input_operation"),
    ("semantics.transform.expander_support", "resized_expanded_values"),
    ("analysis.phi_resolver", "_combine_expansions"),
    ("analysis.condition.tracker", "_build_refined_branch_condition"),
    ("analysis.recurrence.coordinator", "_impl__zero_extend_bitpattern"),
    ("analysis.recurrence.coordinator", "_impl__truncate_to_width"),
    ("analysis.recurrence.coordinator", "_impl__scale_term"),
    ("analysis.recurrence.coordinator", "_impl__build_parity_split_loop_value"),
    ("analysis.recurrence.affine_progression", "_impl__summarize_affine_loop_state_phi"),
    ("analysis.recurrence.affine_progression", "_impl__build_affine_delta_expression"),
    ("analysis.recurrence.counted_loop", "_impl__validate_counted_loop_update_cases"),
    ("analysis.recurrence.guard_proof", "_impl__negated_return_region_condition"),
    ("analysis.recurrence.readonly_reduction", "_impl__build_readonly_reduction_expression_from_terms"),
    ("analysis.recurrence.state_transition", "_impl__add_state_transition_accumulator_seed"),
    ("analysis.recurrence.state_transition", "_impl__combine_conditions_for_state_transition"),
    ("semantics.normalize.arithmetic", "_simplify_mult_identities"),
    ("proof.strategies.pairwise_services.loop_summary", "_impl__unroll_counted_state_transition_value"),
]


#: 「この場で作った式」を表す factory / 派生 API。
_FRESH_CALLS = frozenset(
    {
        "constant", "parameter", "variable", "binary_op", "unary_op", "call",
        "intrinsic", "memory", "phi", "unknown", "clone_with", "derive_with",
        "deepcopy",
    }
)

#: 凍結後に書き換えられない意味 field のうち、これらの site が触っていたもの。
_GUARDED_FIELDS = frozenset({"size", "name", "value", "operands", "runtime_ref", "storage_info"})


def _locally_constructed_names(tree: "ast.AST") -> set:
    import ast

    names = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target = node.targets[0]
            value = node.value
            if (
                isinstance(target, ast.Name)
                and isinstance(value, ast.Call)
                and isinstance(value.func, ast.Attribute)
                and value.func.attr in _FRESH_CALLS
            ):
                names.add(target.id)
    return names


def test_no_shared_object_mutation_site_assigns_semantic_fields_directly():
    """共有され得る式へ直接 `x.size = ...` と書く site が残っていないこと。

    ここに並ぶのは「引数や helper の戻り値（= 他所と共有され得る式）へ幅などを
    書き足していた」関数。凍結済みの式が来ると内部バグになるので、値を作り直す
    入口（`derive_with` / `clone_with`）を通すよう直してある。

    その場で作った式（`x = Expression.binary_op(...)` の直後に幅を入れる等）は
    構築中なので対象外。判定は AST で行うので、行が動いただけでは落ちない。
    """

    import ast
    import importlib
    import inspect
    import textwrap

    offenders = []
    for module_path, function_name in MUTATION_SITES:
        module = importlib.import_module(f"scripts.function_tracer_pcode.{module_path}")
        function = getattr(module, function_name, None)
        if function is None:
            for attribute in vars(module).values():
                candidate = getattr(attribute, function_name, None)
                if callable(candidate):
                    function = candidate
                    break
        assert function is not None, f"{module_path}.{function_name} not found"
        tree = ast.parse(textwrap.dedent(inspect.getsource(function)))
        fresh = _locally_constructed_names(tree)
        for node in ast.walk(tree):
            if not isinstance(node, ast.Assign):
                continue
            for target in node.targets:
                if not (isinstance(target, ast.Attribute) and target.attr in _GUARDED_FIELDS):
                    continue
                base = target.value
                if isinstance(base, ast.Name) and base.id in fresh:
                    continue  # この関数の中で作った式（まだ公開していない）
                offenders.append(
                    f"{module_path}.{function_name}:{ast.unparse(target)}"
                )
    assert offenders == [], (
        "these sites still write a semantic field onto an expression they do not own; "
        "use derive_with(...) / clone_with(...): " + ", ".join(offenders)
    )


def test_the_mutation_site_guard_actually_catches_a_reintroduced_write():
    """guard 自身が効いていることの確認（空振りの AST test にしない）。"""

    import ast
    import textwrap

    source = textwrap.dedent(
        """
        def _regressed(value, output_size):
            value.size = output_size
            return value
        """
    )
    tree = ast.parse(source)
    fresh = _locally_constructed_names(tree)
    writes = [
        ast.unparse(target)
        for node in ast.walk(tree)
        if isinstance(node, ast.Assign)
        for target in node.targets
        if isinstance(target, ast.Attribute)
        and target.attr in _GUARDED_FIELDS
        and not (isinstance(target.value, ast.Name) and target.value.id in fresh)
    ]
    assert writes == ["value.size"]


# ---------------------------------------------------------------------------
# B10: canonical value は container 種別を落とさない
# ---------------------------------------------------------------------------


def test_canonical_value_key_keeps_the_container_kind():
    assert canonical_value_key([1, 2])[0] == "list"
    assert canonical_value_key((1, 2))[0] == "tuple"
    assert canonical_value_key({"a": 1})[0] == "dict"
    assert canonical_value_key({1, 2})[0] == "set"
    assert canonical_value_key(frozenset({1, 2}))[0] == "frozenset"
    # 旧 `_atom_key` が区別していた list / tuple は新実装でも区別される。
    assert canonical_value_key([1, 2]) != canonical_value_key((1, 2))


def test_canonical_value_key_of_an_opaque_object_is_process_independent():
    class Opaque:
        pass

    first = canonical_value_key(Opaque())
    second = canonical_value_key(Opaque())
    assert first == second
    assert value_key_is_opaque(first)
    # 型名だけを持ち、`id()` を含まない。
    assert all(not isinstance(item, int) for item in first)


def test_freeze_folds_a_list_value_into_a_tuple_but_keeps_the_kind_tag():
    expr = Expression(ExpressionType.LITERAL, value=[1, 2], size=4)
    before = semantic_projection(expr).canonical_value
    expr.freeze()
    after = semantic_projection(expr).canonical_value
    assert before == after
    assert after[0] == "list"


# ---------------------------------------------------------------------------
# B13: PHI consumer の互換（PhiBranch は tuple のまま）
# ---------------------------------------------------------------------------


def test_phi_branch_behaves_like_the_plain_tuple_consumers_expect():
    outer, guard, left, right, _inner = _phi_expression()
    outer.freeze()
    branch = outer.value[0]

    assert isinstance(branch, tuple)
    assert len(branch) == 2
    condition, value = branch
    assert condition is guard
    assert branch[0] is guard
    assert branch[1] is value
    assert branch.condition is guard
    assert branch.value is value


def test_phi_to_dict_still_renders_branches():
    outer, _guard, _left, _right, _inner = _phi_expression()
    payload_before = outer.to_dict()
    outer.freeze()
    payload_after = outer.to_dict()
    assert payload_before == payload_after
    assert payload_after["type"] == "PHI"
    assert len(payload_after["value"]) == 2


def test_phi_factory_normalises_branches_before_freeze():
    left = Expression.parameter("a", 0, size=4)
    phi = Expression.phi([(None, left)])
    assert isinstance(phi.value, tuple)
    assert isinstance(phi.value[0], PhiBranch)
