# -*- coding: utf-8 -*-
"""Issue #281: operand の差し替え（`derive_with_operands`）と構造 key の順序（`structural_sort_key`）。

#281 の機序: bounded refinement が caller の node を operand だけ差し替えて作り直すとき `opcode` を
落としていた。`("intrinsic", "PTRADD", None, …)` と `("intrinsic", "PTRADD", 65, …)` が同じ条件集合に
並び、`conditions_signature` の `sort()` が `None` と `int` を比べて `TypeError` になった。

* 派生の方針は `core/operand_derivation.py` の表を、field と ref の型ごとに固定する
* 修正前に落ちる組（既存の API だけで書いたもの）は `test_issue281_conditions_signature.py`
"""

import itertools
import os
import subprocess
import sys
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis.bounded_refinement import (
    BoundedCallRefiner,
    ExpressionExpansion,
)
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.core import (
    AddressValueRef,
    CanonicalLocation,
    Condition,
    CountedLoopSummaryRef,
    Expression,
    ExpressionType,
    LocationBaseRef,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    PostStateValueRef,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.core.intrinsics import PTRADD_OPCODE, PTRSUB_OPCODE
from scripts.function_tracer_pcode.analysis.effects.location import _address_root_is_stack_frame
from scripts.function_tracer_pcode.core.operand_derivation import (
    REFUSED_ADDRESS_CHANGED,
    REFUSED_OPERAND_DEPENDENT_REF,
    REFUSED_OPERAND_DEPENDENT_STORAGE,
    RUNTIME_REF_POLICY,
    OperandDerivationRefused,
)
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.structural import (
    StructuralKeyNotOrderable,
    exact_structural_identity,
    expression_key,
    structural_sort_key,
    unidentified_identity,
)
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))


def _param(name: str = "n", index: int = 0, size: int = 8) -> Expression:
    return Expression.parameter(name, index=index, data_type="long", size=size)


def _const(value: int, size: int = 8) -> Expression:
    return Expression.constant(value, size=size)


def _ptradd(base: Expression, *, opcode=PTRADD_OPCODE, runtime_ref=None) -> Expression:
    return Expression.intrinsic("PTRADD", [base, _const(4), _const(8)], size=8, opcode=opcode, runtime_ref=runtime_ref)


def _eq_zero(expr: Expression, negated: bool = False) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", expr, _const(0, size=expr.size or 8)), negated=negated)


def _loc(name: str = "n", offset: int = 0, size: int = 8) -> CanonicalLocation:
    return CanonicalLocation(base_ref=LocationBaseRef.parameter(name, index=0), offset=offset, size=size)


# ---------------------------------------------------------------------------
# structural_sort_key の契約
# ---------------------------------------------------------------------------


def _generated_keys():
    x = _param("x", 0)
    exprs = [
        x,
        _const(0),
        _const(1),
        _const(-1),
        _ptradd(x, opcode=None),
        _ptradd(x, opcode=PTRADD_OPCODE),
        Expression.memory(x, size=8, read_order_key=None),
        Expression.memory(x, size=8, read_order_key=3),
        Expression.memory(x, size=8, runtime_ref=ObservedMemoryReadRef(order_key=2)),
        Expression.binary_op("INT_ADD", x, _const(1)),
        Expression.unknown("u"),
        Expression.binary_op("INT_ADD", *([x] * 2)),
    ]
    keys = [expression_key(e) for e in exprs]
    keys.append(expression_key(Expression.binary_op("INT_ADD", x, x), budget=1))  # 打ち切った key
    keys += [("none",), unidentified_identity("test")]
    keys += [(k, "INT_EQUAL", ("none",), True) for k in list(keys)]
    return keys


def test_structural_sort_key_is_injective_and_agrees_with_key_equality():
    keys = _generated_keys()
    for left, right in itertools.product(keys, repeat=2):
        assert (structural_sort_key(left) == structural_sort_key(right)) == (left == right)


def test_structural_sort_key_rejects_values_outside_the_canonical_encoding():
    for value in (object(), frozenset({1}), {"a": 1}, (1, object())):
        with pytest.raises(StructuralKeyNotOrderable):
            structural_sort_key(value)
    assert not issubclass(StructuralKeyNotOrderable, TypeError)


def test_structural_sort_key_is_deterministic_across_processes():
    script = (
        "import json, sys\n"
        "from scripts.function_tracer_pcode.core import Expression\n"
        "from scripts.function_tracer_pcode.core.intrinsics import PTRADD_OPCODE\n"
        "from scripts.function_tracer_pcode.core.structural import expression_key, structural_sort_key\n"
        "x = Expression.parameter('x', index=0, data_type='long', size=8)\n"
        "c = Expression.constant\n"
        "e = Expression.intrinsic('PTRADD', [x, c(4, size=8), c(8, size=8)], size=8, opcode=PTRADD_OPCODE)\n"
        "print(structural_sort_key(expression_key(e)).hex())\n"
    )
    outputs = set()
    for seed in ("0", "1"):
        env = dict(os.environ, PYTHONHASHSEED=seed, PYTHONPATH=REPO_ROOT)
        outputs.add(
            subprocess.run(
                [sys.executable, "-B", "-c", script], env=env, cwd=REPO_ROOT, check=True,
                capture_output=True, text=True,
            ).stdout.strip()
        )
    here = structural_sort_key(expression_key(_ptradd(Expression.parameter("x", index=0, data_type="long", size=8))))
    assert outputs == {here.hex()}


# ---------------------------------------------------------------------------
# AC4: derive_with_operands の方針（field と ref の型ごと）
# ---------------------------------------------------------------------------


def test_derive_keeps_every_operand_independent_field():
    expr = Expression(
        ExpressionType.INTRINSIC,
        value=None,
        operator=None,
        operands=[_param("a"), _const(4), _const(8)],
        size=8,
        name="PTRADD",
        data_type="long *",
        read_order_key=7,
        opcode=PTRADD_OPCODE,
        call_argument_width_evidence=("evidence",),
    )
    derived = expr.derive_with_operands([_param("b"), _const(4), _const(8)])
    assert derived is not expr
    for field in ("expr_type", "value", "operator", "size", "name", "data_type",
                  "read_order_key", "opcode", "call_argument_width_evidence"):
        assert getattr(derived, field) == getattr(expr, field), field
    assert derived.operands[0].name == "b"
    assert expr.operands[0].name == "a"


def test_identical_operands_return_the_same_expression():
    expr = _ptradd(_param())
    assert expr.derive_with_operands(list(expr.operands)) is expr


def test_derive_rejects_an_arity_change():
    expr = _ptradd(_param())
    with pytest.raises(ValueError):
        expr.derive_with_operands([_param("m")])


def test_recurrence_semantic_key_is_invalidated_when_operands_change():
    expr = Expression(
        ExpressionType.BINARY_OP, operator="INT_ADD", operands=[_param(), _const(1)], size=8,
        recurrence_semantic_key=("recurrence", "n+1"),
    )
    assert expr.derive_with_operands(list(expr.operands)).semantic_key() == ("recurrence", "n+1")
    derived = expr.derive_with_operands([_param("m"), _const(1)])
    assert getattr(derived, "_recurrence_semantic_key", None) is None


def _address_resolver():
    holder = SimpleNamespace()
    holder._resolve_concrete_address_offset = (
        lambda e: PcodeTracer._resolve_concrete_address_offset(holder, e)
    )
    return holder


@pytest.mark.parametrize(
    "name,opcode,arity",
    [
        ("PTRADD", PTRADD_OPCODE, 3),
        ("PTRSUB", PTRSUB_OPCODE, 2),
        # opcode の無い PTRADD も production に居る（consumer は名前でも見分ける）
        ("PTRADD", None, 3),
    ],
)
def test_pointer_address_ref_is_invalidated_and_resolution_follows_the_operands(name, opcode, arity):
    old_operands = [_const(0x1000), _const(2), _const(4)][:arity]
    new_operands = [_const(0x2000), _const(2), _const(4)][:arity]
    old_offset = 0x1000 + (2 * 4 if arity == 3 else 2)
    new_offset = 0x2000 + (2 * 4 if arity == 3 else 2)
    expr = Expression.intrinsic(
        name, old_operands, size=8, opcode=opcode, runtime_ref=AddressValueRef(address_offset=old_offset),
    )
    resolver = _address_resolver()

    derived = expr.derive_with_operands(new_operands)

    assert derived.runtime_ref is None
    assert derived.opcode == opcode
    # 正例: ref を落としても番地は operand から同じ規則で解決される
    assert resolver._resolve_concrete_address_offset(derived) == new_offset
    # 負例（修正前の振る舞い）: ref を残す複製は古い番地に解決される
    stale = expr.clone_with(operands=new_operands)
    assert resolver._resolve_concrete_address_offset(stale) == old_offset


def test_address_value_ref_on_another_node_is_refused():
    expr = Expression.binary_op("INT_ADD", _param(), _const(4))
    expr = expr.clone_with(runtime_ref=AddressValueRef(address_offset=0x1000))
    with pytest.raises(OperandDerivationRefused) as raised:
        expr.derive_with_operands([_param("m"), _const(4)])
    assert raised.value.reason == REFUSED_OPERAND_DEPENDENT_REF


def test_observed_read_without_location_keeps_its_load_position():
    ref = ObservedMemoryReadRef(order_key=5)
    expr = Expression.memory(_param(), size=8, read_order_key=5, runtime_ref=ref)
    derived = expr.derive_with_operands([_param("m")])
    assert derived.runtime_ref is ref
    assert derived.read_order_key == 5


LOCATED_MEMORY_REFS = [
    pytest.param(lambda: ObservedMemoryReadRef(order_key=5, location=_loc()), id="observed-with-location"),
    pytest.param(
        lambda: ObservedMemoryReadRef(order_key=5, snapshot_ref=PostStateSnapshotRef.function_return()),
        id="observed-with-snapshot",
    ),
    pytest.param(
        lambda: PostStateReadRef(location=_loc(), snapshot_ref=PostStateSnapshotRef.function_return()),
        id="post-state-read",
    ),
    pytest.param(lambda: PostStateValueRef(location=_loc()), id="post-state-value"),
    pytest.param(lambda: _loc(), id="canonical-location"),
]


@pytest.mark.parametrize("make_ref", LOCATED_MEMORY_REFS)
def test_located_memory_ref_refuses_a_changed_address(make_ref):
    ref = make_ref()
    expr = Expression.memory(_param("n"), size=8, runtime_ref=ref)
    with pytest.raises(OperandDerivationRefused) as raised:
        expr.derive_with_operands([_param("m", index=1)])
    assert raised.value.reason == REFUSED_ADDRESS_CHANGED
    # 負例（修正前の振る舞い）: 複製は location が n を指したまま、番地だけが m になる
    stale = expr.clone_with(operands=[_param("m", index=1)])
    assert stale.runtime_ref is ref


@pytest.mark.parametrize("make_ref", LOCATED_MEMORY_REFS)
def test_located_memory_ref_is_kept_only_when_the_address_is_the_same_object(make_ref):
    ref = make_ref()
    address = Expression.binary_op("INT_ADD", _param("n"), _const(8))
    expr = Expression.memory(address, size=8, runtime_ref=ref)
    # 正例: 番地が同じ object なら派生は起きず、ref と番地の組はそのまま
    assert expr.derive_with_operands([address]) is expr
    # 構造が同じでも別の object なら変わったとみなす（番地を読む consumer が読む field を構造 key が持たない
    # ことがある: 下の test。値を失わない費用として拒否し、呼び出し側は元の式に戻る）
    rebuilt = Expression.binary_op("INT_ADD", _param("n"), _const(8))
    with pytest.raises(OperandDerivationRefused) as raised:
        expr.derive_with_operands([rebuilt])
    assert raised.value.reason == REFUSED_ADDRESS_CHANGED
    # 確かめるのは API 自身: 呼び出し側から「番地は変わらない」と申告する経路は無く、operand も凍結しない
    assert not rebuilt.is_frozen


@pytest.mark.parametrize("make_ref", LOCATED_MEMORY_REFS)
def test_located_memory_ref_refuses_an_address_that_differs_only_in_a_runtime_ref(make_ref):
    """review の再現: 同名・同形の VARIABLE で `AddressValueRef` だけが違う番地。"""

    def _global(offset):
        return Expression.variable("g", size=8).clone_with(runtime_ref=AddressValueRef(address_offset=offset))

    ref = make_ref()
    old_address, new_address = _global(0x1000), _global(0x2000)
    expr = Expression.memory(old_address, size=8, runtime_ref=ref)
    # 番地を読む consumer は ref を読むので、2 つの番地は違う
    resolver = _address_resolver()
    assert resolver._resolve_concrete_address_offset(old_address) == 0x1000
    assert resolver._resolve_concrete_address_offset(new_address) == 0x2000
    # 負例（修正前の判定）: 既定の厳密な構造 identity は 2 つを等しいとし、古い location を残していた
    assert exact_structural_identity(old_address) == exact_structural_identity(new_address)
    with pytest.raises(OperandDerivationRefused) as raised:
        expr.derive_with_operands([new_address])
    assert raised.value.reason == REFUSED_ADDRESS_CHANGED


def test_storage_info_on_a_value_node_is_refused():
    """operand を持つ node の `storage_info` は「この値の在りか」の主張で、operand が変われば古い。"""

    stack = StorageInfo(is_register=False, space_name="stack", offset=-16, size=8)
    expr = Expression.unary_op("INT_ZEXT", _param("a", size=4)).clone_with(size=8, storage_info=stack)
    replacement = Expression.binary_op("INT_ADD", _param("b", size=4), _const(4, size=4))
    with pytest.raises(OperandDerivationRefused) as raised:
        expr.derive_with_operands([replacement])
    assert raised.value.reason == REFUSED_OPERAND_DEPENDENT_STORAGE
    # 負例（写す複製）: 古い stack の主張が残り、新しい値の番地まで stack の frame と判定される
    stale = expr.clone_with(operands=[replacement])
    assert _address_root_is_stack_frame(stale) is True
    assert _address_root_is_stack_frame(Expression.unary_op("INT_ZEXT", replacement)) is False


def test_unidentifiable_address_counts_as_changed():
    ref = PostStateReadRef(location=_loc(), snapshot_ref=PostStateSnapshotRef.function_return())
    opaque = Expression(ExpressionType.UNKNOWN, name="opaque", value=object(), size=8)
    expr = Expression.memory(opaque, size=8, runtime_ref=ref)
    twin = Expression(ExpressionType.UNKNOWN, name="opaque", value=opaque.value, size=8)
    with pytest.raises(OperandDerivationRefused):
        expr.derive_with_operands([twin])


def test_loop_summary_intrinsic_refuses_changed_operands():
    expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), _param("p", size=4)],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1, result_size=4, signed_loop=True, residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
    )
    with pytest.raises(OperandDerivationRefused) as raised:
        expr.derive_with_operands([_const(0, size=4), _const(0, size=4), _param("q", size=4)])
    assert raised.value.ref_type == "CountedLoopSummaryRef"


def test_unlisted_runtime_ref_is_refused():
    expr = Expression.binary_op("INT_ADD", _param(), _const(4)).clone_with(
        runtime_ref=UnknownValueRef.opaque(reason="test", display_hint="test")
    )
    with pytest.raises(OperandDerivationRefused):
        expr.derive_with_operands([_param("m"), _const(4)])


def test_policy_table_names_exactly_the_documented_ref_types():
    assert {kind.__name__ for kind in RUNTIME_REF_POLICY} == {
        "NoneType",
        "AddressValueRef",
        "ObservedMemoryReadRef",
        "PostStateReadRef",
        "PostStateValueRef",
        "CanonicalLocation",
        "LocationBaseRef",
    }


def test_location_base_identity_on_a_value_is_refused():
    # tracer は幅を合わせた parameter の値に「この値は parameter n」という base の ref を付ける
    expr = Expression.binary_op("INT_AND", _param(), _const(0xFFFFFFFF)).clone_with(
        runtime_ref=LocationBaseRef.parameter("n", index=0)
    )
    with pytest.raises(OperandDerivationRefused) as raised:
        expr.derive_with_operands([_param("m", index=1), _const(0xFFFFFFFF)])
    assert raised.value.ref_type == "LocationBaseRef"
    assert expr.derive_with_operands(list(expr.operands)) is expr


# ---------------------------------------------------------------------------
# 拒否したとき、候補の一部だけを捨てない
# ---------------------------------------------------------------------------


def test_one_refused_candidate_keeps_the_node_unexpanded_instead_of_dropping_it():
    address = _param("n")
    expr = Expression.memory(
        address, size=8, runtime_ref=PostStateReadRef(location=_loc(), snapshot_ref=PostStateSnapshotRef.function_return())
    )
    refiner = BoundedCallRefiner(lambda *_: None, max_unroll=1, max_cases=8, debug=False)
    analysis = create_mock_analysis("caller")
    other_address = _param("m", index=1)
    guard_same = _eq_zero(_param("k", index=2))
    guard_other = _eq_zero(_param("k", index=2), negated=True)
    original_expand = refiner._expand_expression

    def expand(node, analysis_, fuel, trail):
        if node is address:
            # 番地の展開が 2 通り: 1 つは元の番地（派生できる）、もう 1 つは別の番地（ref を保てない）
            return [
                ExpressionExpansion(address, [guard_same], frozenset({1})),
                ExpressionExpansion(other_address, [guard_other], frozenset({2})),
            ]
        return original_expand(node, analysis_, fuel, trail)

    refiner._expand_expression = expand

    expansions = expand(expr, analysis, 1, set())

    # 派生できた候補（guard_same の枝）だけが残ると、guard_other の枝の値が黙って消える
    assert len(expansions) == 1
    assert expansions[0].value is expr
    assert expansions[0].conditions == []
    assert expansions[0].callees == frozenset()
    assert any(
        note.startswith("bounded_call_refinement_operand_derivation_refused:" + REFUSED_ADDRESS_CHANGED)
        for note in analysis.analysis_notes
    )


def test_unrefused_candidates_are_all_kept():
    address = _param("n")
    expr = Expression.memory(address, size=8, runtime_ref=ObservedMemoryReadRef(order_key=1))
    refiner = BoundedCallRefiner(lambda *_: None, max_unroll=1, max_cases=8, debug=False)
    analysis = create_mock_analysis("caller")
    other_address = _param("m", index=1)
    original_expand = refiner._expand_expression

    def expand(node, analysis_, fuel, trail):
        if node is address:
            return [
                ExpressionExpansion(address, [_eq_zero(_param("k", index=2))], frozenset({1})),
                ExpressionExpansion(other_address, [_eq_zero(_param("k", index=2), negated=True)], frozenset({2})),
            ]
        return original_expand(node, analysis_, fuel, trail)

    refiner._expand_expression = expand
    expansions = expand(expr, analysis, 1, set())
    assert [e.value.operands[0] for e in expansions] == [address, other_address]
    assert expansions[0].value is expr
