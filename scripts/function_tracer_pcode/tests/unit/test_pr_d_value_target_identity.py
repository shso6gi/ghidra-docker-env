# -*- coding: utf-8 -*-
"""値の identity と対象の identity（Issue #218、計画 v4 PR-D）。

旧 `expression_provenance_key` は 2 つの役割を兼ねていた:

* 式が **指す対象**（reason / blocker の target）: owner つきの ref・storage があれば式の形に依らずそれ
* 式の **値**（case identity・dedup・拡張の証拠・引数の値）

対象の早期 return を値の consumer が読むと、`ZEXT(p)` と `SEXT(p)` のような値の違う式が同じ key になる。
さらに予算を超えた式は sha256 の一致だけで同じとされていた。PR-D はこれを `object_target_key`（T）と
`value_identity`（V）に分け、V は早期 return を持たず、超予算では厳密比較の intern の token を使う。

この file の test は 4 つの組（計画 v4 §11.2 の D 行）:

* (a) 反例: 修正前の main で FAIL する（早期 return の 9 形 + storage、digest の強制衝突）
* (b) 対照: 予算内の式は旧 key と byte 一致（D1）、同じ値は同じ identity
* (c) production の consumer: monolithic の case identity 2 つ、呼び出しの引数の dedup、call-effect の
      引数の束、書き換えの照合、guard overlap の cache、exact query の attempt cache
* (d) mutation は tools 側（consumer を T に戻すと (a)(c) が落ちる）
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.core import COUNTED_LOOP_SUM_OPCODE, PTRADD_OPCODE
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.runtime_refs import (
    AddressValueRef,
    CountedLoopSummaryRef,
    LocationBaseRef,
    UnknownValueRef,
)
from scripts.function_tracer_pcode.core.semantic_freeze import publish
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.structural import (
    expression_key_safe,
    label_view,
    object_target_key,
    value_identity,
)
from scripts.function_tracer_pcode.proof.monolithic_authority import _case_identity
from scripts.function_tracer_pcode.proof.strategies.monolithic_support import _monolithic_case_identity


REPO_ROOT = Path(__file__).resolve().parents[4]


# ---------------------------------------------------------------------------
# 形の部品
# ---------------------------------------------------------------------------


def _param_ref(index=0, program=1):
    return LocationBaseRef.parameter("param_1", index=index, owner_program_id=program, owner_entry_offset=0x100)


def _param(name="param_1", index=0, size=4, ref=None):
    return Expression.parameter(name, index, "int", size=size, runtime_ref=ref if ref is not None else _param_ref(index))


def _with_ref(expr, ref, size=None):
    if size is not None:
        expr.size = size
    expr.runtime_ref = ref
    return expr


def _subpiece(offset):
    return _with_ref(
        Expression.binary_op("SUBPIECE", _param(size=8), Expression.constant(offset, size=8)), _param_ref(), size=4,
    )


def _extend(operator):
    return _with_ref(Expression.unary_op(operator, _param(size=4)), _param_ref(), size=8)


def _counted_loop(argument, residue=((2, 0, 1, 0), (2, 1, -1, 0))):
    ref = CountedLoopSummaryRef(induction_step=1, result_size=4, signed_loop=True, residue_cases=residue)
    return Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [Expression.constant(0, size=4), Expression.constant(0, size=4), argument],
        size=4, runtime_ref=ref, opcode=COUNTED_LOOP_SUM_OPCODE,
    )


_ADDRESS = AddressValueRef(address_offset=0x1000, program_id=1, space_name="ram")


def _ptradd(index):
    return Expression.intrinsic(
        "PTRADD",
        [Expression.parameter("base", 0, "int*", size=8), Expression.constant(index, size=8), Expression.constant(8, size=8)],
        size=8, runtime_ref=_ADDRESS, opcode=PTRADD_OPCODE,
    )


def _memory(pointer_name, size, order):
    return Expression.memory(
        Expression.parameter(pointer_name, 0, "int*", size=8), size=size, read_order_key=order, runtime_ref=_ADDRESS,
    )


def _unknown(size):
    expr = Expression.unknown("u", runtime_ref=UnknownValueRef.opaque(reason="r", display_hint="u"))
    expr.size = size
    return expr


_STACK = StorageInfo(is_register=False, space_name="stack", space_id=2, offset=-8, size=4)


def _stored(expr):
    expr.storage_info = _STACK
    return expr


#: 対象（ref / storage）は同じだが値の違う式の組。旧 provenance key は早期 return で同じ key にした
#: （計画 v4 §4.5 の `t1/t2/t3`、全 9 形 + storage。main `44e25245` で mono / auth の case identity が一致）
SAME_TARGET_DIFFERENT_VALUE = {
    "param_vs_subpiece": lambda: (_param(size=8), _subpiece(0)),
    "subpiece_offsets": lambda: (_subpiece(0), _subpiece(4)),
    "zext_vs_sext": lambda: (_extend("INT_ZEXT"), _extend("INT_SEXT")),
    "same_ref_other_name": lambda: (_param("param_1"), _param("param_2", ref=_param_ref(0))),
    "unknown_widths": lambda: (_unknown(4), _unknown(8)),
    "loop_count_operand": lambda: (
        _counted_loop(Expression.parameter("param_1", 0, "int", size=4)),
        _counted_loop(Expression.parameter("param_2", 1, "int", size=4)),
    ),
    "loop_count_constant": lambda: (
        _counted_loop(Expression.constant(3, size=4)), _counted_loop(Expression.constant(7, size=4)),
    ),
    "ptradd_index": lambda: (_ptradd(1), _ptradd(2)),
    "memory_width_and_order": lambda: (_memory("p", 4, 1), _memory("p", 8, 2)),
    "memory_address_operand": lambda: (_memory("p", 4, 1), _memory("q", 4, 1)),
    "storage": lambda: (
        _stored(_with_ref(Expression.unary_op("INT_ZEXT", Expression.variable("x", size=4)), None, size=8)),
        _stored(Expression.binary_op("INT_ADD", Expression.variable("y", size=4), Expression.constant(1, size=4))),
    ),
}


def _case(value):
    return SimpleNamespace(index=0, source_indices=(0,), value_expr=value, conditions=())


def _pair(name, frozen):
    left, right = SAME_TARGET_DIFFERENT_VALUE[name]()
    if frozen:
        left, right = publish(left), publish(right)
    return left, right


# ---------------------------------------------------------------------------
# (a) 反例: 早期 return が値の consumer に届く
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("name", sorted(SAME_TARGET_DIFFERENT_VALUE))
def test_case_identities_tell_values_apart_that_share_an_object_target(name, frozen):
    left, right = _pair(name, frozen)
    # 対照: 対象は同じ（reason の target としては同じ対象を指す）
    assert object_target_key(left) == object_target_key(right)
    # 値は違う（#218 AC3: case identity が別の値で一致しない）
    assert value_identity(left) != value_identity(right)
    assert _monolithic_case_identity(_case(left)) != _monolithic_case_identity(_case(right))
    assert _case_identity(_case(left)) != _case_identity(_case(right))


@pytest.mark.parametrize("name", sorted(SAME_TARGET_DIFFERENT_VALUE))
def test_the_same_value_keeps_its_case_identity(name):
    # 対照: 同じ形の式を作り直しても同じ identity（値の共有を失わない）
    first, _ = SAME_TARGET_DIFFERENT_VALUE[name]()
    again, _ = SAME_TARGET_DIFFERENT_VALUE[name]()
    assert value_identity(first) == value_identity(again)
    assert _monolithic_case_identity(_case(first)) == _monolithic_case_identity(_case(again))
    assert _case_identity(_case(publish(first))) == _case_identity(_case(publish(again)))


def test_value_identity_has_no_early_return_on_refs_or_storage():
    # 早期 return の印（対象の tag）は値の identity に出ない
    for name in SAME_TARGET_DIFFERENT_VALUE:
        left, _ = SAME_TARGET_DIFFERENT_VALUE[name]()
        assert value_identity(left)[0] in {"expression", "expression_exact"}, name


# ---------------------------------------------------------------------------
# (a) 反例: digest の一致で同じとしない（D5）
# ---------------------------------------------------------------------------


class _ConstantSha:
    """`hashlib.sha256` の代わり: どの入力にも同じ digest（強制衝突）。"""

    def __init__(self, data=b""):
        pass

    def update(self, data):
        pass

    def hexdigest(self):
        return "0" * 64

    def digest(self):
        return b"\x00" * 32


def _deep_chain(leaf, depth, operator="INT_ADD"):
    expr = leaf
    for index in range(depth):
        expr = Expression.binary_op(operator, expr, Expression.constant(index, size=4))
    return expr


@pytest.fixture
def forced_digest_collision(monkeypatch):
    """structural の sha256（exact tail と record の intern）を定数にする。"""

    monkeypatch.setattr(structural.hashlib, "sha256", _ConstantSha)
    # 既に memo された token を使わない（強制衝突の下で新しく intern させる）
    monkeypatch.setattr(structural, "_TAIL_INTERN", structural._ExactTailIntern())
    monkeypatch.setattr(structural, "_VALIDATED_TAIL_MEMO", structural.WeakKeyedTable())
    yield


def test_beyond_budget_values_differ_under_a_forced_digest_collision(forced_digest_collision):
    # 予算（256）を超えた式: 構造の違う 2 つは別の identity、同じ構造は同じ identity（暗号の仮定を置かない）
    left = _deep_chain(Expression.parameter("p", 0, "int", size=4), 400, "INT_ADD")
    right = _deep_chain(Expression.parameter("p", 0, "int", size=4), 400, "INT_SUB")
    same = _deep_chain(Expression.parameter("p", 0, "int", size=4), 400, "INT_ADD")
    assert expression_key_safe(left) is None
    assert value_identity(left)[0] == "expression_exact"
    assert value_identity(left) != value_identity(right)
    assert value_identity(left) == value_identity(same)
    assert _monolithic_case_identity(_case(left)) != _monolithic_case_identity(_case(right))
    assert _case_identity(_case(left)) != _case_identity(_case(right))
    assert object_target_key(left) != object_target_key(right)


def test_the_exact_record_intern_compares_bytes_under_a_forced_digest_collision(forced_digest_collision):
    intern = structural.ExactRecordIntern()
    one = intern.token("d", b"one")
    two = intern.token("d", b"two")
    assert one[1] == two[1]  # 同じ bucket（digest を定数にした）
    assert one != two
    assert intern.token("d", b"one") == one
    assert intern.token("e", b"one") != one  # domain も record の一部


# ---------------------------------------------------------------------------
# (b) 対照: 予算内の式は旧 provenance key と byte 一致（D1）
# ---------------------------------------------------------------------------


def _old_budget_key(expr):
    """旧 `expression_provenance_key` の早期 return の無い予算内の経路（main `44e25245` の定義）。"""

    safe = expression_key_safe(expr, budget=256, include_memory_read_order=True, include_semantic_runtime_refs=True)
    return None if safe is None else ("expression", safe)


D1_CONTROLS = {
    "arith": lambda: Expression.binary_op(
        "INT_ADD", Expression.parameter("a", 0, "int", size=4), Expression.constant(5, size=4)
    ),
    "unknown_with_ref": lambda: Expression.binary_op(
        "INT_MULT", _unknown(4), Expression.parameter("a", 0, "int", size=4)
    ),
    "memory_with_ref": lambda: Expression.unary_op("INT_ZEXT", _memory("p", 4, 3)),
    "nested_param_with_ref": lambda: Expression.binary_op("INT_SUB", _param(), Expression.constant(1, size=4)),
    "ptradd_with_address_ref": lambda: Expression.binary_op("INT_ADD", _ptradd(3), Expression.constant(1, size=8)),
}


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("name", sorted(D1_CONTROLS))
def test_budget_values_without_rendered_refs_keep_the_old_key_bytes(name, frozen):
    expr = D1_CONTROLS[name]()
    if frozen:
        expr = publish(expr)
    assert value_identity(expr) == _old_budget_key(expr)
    assert json.dumps(value_identity(expr)) == json.dumps(_old_budget_key(expr))


# ---------------------------------------------------------------------------
# 描画が ref から読む成分（値が同じ ⇒ 同じ項: 計画 v4 I1）
# ---------------------------------------------------------------------------


class _GlobalAddress(AddressValueRef):
    def global_object_identity(self):
        return ("g", 4, 0)


def _global_constant():
    return Expression(
        ExpressionType.CONSTANT, value=0x1000, size=8,
        runtime_ref=_GlobalAddress(address_offset=0x1000, program_id=1, space_name="ram"),
    )


RENDERED_REF_PAIRS = {
    # 名前付き global のアドレス（`gaddr_*`）と同じ値のふつうの定数
    "global_address_constant": lambda: (
        _global_constant(), Expression(ExpressionType.CONSTANT, value=0x1000, size=8),
    ),
    # residue だけ違う COUNTED_LOOP_SUM（構造 key は同じ、SMT は違う: #247 AC1 の形）
    "loop_residue_root": lambda: (
        _counted_loop(Expression.parameter("param_1", 0, "int", size=4)),
        _counted_loop(Expression.parameter("param_1", 0, "int", size=4), residue=((2, 0, 1, 0), (2, 1, 1, 0))),
    ),
    # 同じ形が入れ子にあるとき（旧 provenance key の根の早期 return は見なかった）
    "loop_residue_nested": lambda: (
        Expression.binary_op("INT_ADD", _counted_loop(Expression.parameter("param_1", 0, "int", size=4)),
                             Expression.constant(1, size=4)),
        Expression.binary_op("INT_ADD", _counted_loop(Expression.parameter("param_1", 0, "int", size=4),
                                                       residue=((2, 0, 1, 0), (2, 1, 1, 0))),
                             Expression.constant(1, size=4)),
    ),
    "global_address_nested": lambda: (
        Expression.memory(_global_constant(), size=4, read_order_key=1),
        Expression.memory(Expression(ExpressionType.CONSTANT, value=0x1000, size=8), size=4, read_order_key=1),
    ),
}


@pytest.mark.parametrize("name", sorted(RENDERED_REF_PAIRS))
def test_values_rendered_to_different_terms_never_share_a_value_identity(name):
    left, right = (publish(item) for item in RENDERED_REF_PAIRS[name]())
    assert left.to_smt() != right.to_smt()
    assert value_identity(left) != value_identity(right)
    assert _monolithic_case_identity(_case(left)) != _monolithic_case_identity(_case(right))


RENDER_IGNORED_REF_PAIRS = {
    # 描画が ref を読まない node は ref が違っても同じ値（値の共有を失わない）
    "parameter_ref_program": lambda: (_param(ref=_param_ref(0, 1)), _param(ref=_param_ref(0, 2))),
    "ptradd_address_ref": lambda: (_ptradd(1), Expression.intrinsic(
        "PTRADD",
        [Expression.parameter("base", 0, "int*", size=8), Expression.constant(1, size=8), Expression.constant(8, size=8)],
        size=8, opcode=PTRADD_OPCODE,
    )),
}


@pytest.mark.parametrize("name", sorted(RENDER_IGNORED_REF_PAIRS))
def test_refs_the_renderer_ignores_do_not_split_a_value(name):
    left, right = (publish(item) for item in RENDER_IGNORED_REF_PAIRS[name]())
    assert left.to_smt() == right.to_smt()
    assert value_identity(left) == value_identity(right)


# ---------------------------------------------------------------------------
# 保存後（D6）と費用（D2・D3）
# ---------------------------------------------------------------------------


def test_a_large_value_identity_is_unidentified_across_processes_and_a_small_one_is_stable():
    from scripts.function_tracer_pcode.checker.cause_aggregate import freeze_identity

    deep = _deep_chain(Expression.parameter("p", 0, "int", size=4), 400)
    large = value_identity(deep)
    assert freeze_identity(large) != freeze_identity(large)
    small = value_identity(Expression.binary_op("INT_ADD", Expression.parameter("p", 0, "int", size=4),
                                                Expression.constant(1, size=4)))
    assert freeze_identity(small) == freeze_identity(small)
    child = (
        "import json, sys\nsys.path.insert(0, {root!r})\n"
        "from scripts.function_tracer_pcode.core.expression import Expression\n"
        "from scripts.function_tracer_pcode.core.structural import value_identity\n"
        "e = Expression.binary_op('INT_ADD', Expression.parameter('p', 0, 'int', size=4), Expression.constant(1, size=4))\n"
        "print(json.dumps(value_identity(e)))\n"
    ).format(root=str(REPO_ROOT))
    runs = [
        subprocess.run([sys.executable, "-B", "-c", child], capture_output=True, text=True, check=True).stdout
        for _ in range(2)
    ]
    assert runs[0] == runs[1] == json.dumps(small) + "\n"


def _shared_dag(nodes, leaf="p"):
    """distinct な node が `nodes` 個、各 node が直前の 2 つを共有する DAG（木に展開すると指数個）。"""

    a = Expression.parameter(leaf, 0, "int", size=4)
    b = Expression.constant(1, size=4)
    for index in range(nodes - 2):
        a, b = b, Expression.binary_op("INT_ADD" if index % 2 else "INT_XOR", a, b)
    return b


def test_value_identity_of_a_large_dag_is_linear():
    # D2 は host の 1 回目で 2 s / 4 s（`tools/d2_bench.py`）。ここは 2 乗（旧 digest は 8,401 node で 44 s）を
    # 捕まえる緩い上限だけを置く（wall-clock は負荷で揺れる）
    dag = publish(_shared_dag(9001))
    start = time.perf_counter()
    identity = value_identity(dag)
    assert time.perf_counter() - start < 20.0
    assert identity[0] == "expression_exact"
    chain = _deep_chain(Expression.parameter("p", 0, "int", size=4), 20000)
    start = time.perf_counter()
    assert value_identity(chain)[0] == "expression_exact"
    assert time.perf_counter() - start < 20.0


def test_the_fallback_interns_at_most_one_small_record_per_distinct_node():
    # D3: 足す record ≤ distinct な node 数、record ≤ 400 B
    nodes = 3000
    # 他の test が同じ形を intern していないこと（intern は process 全体）
    dag = _shared_dag(nodes, leaf="d3_only_leaf")
    before = structural.exact_tail_statistics()
    value_identity(dag)
    after = structural.exact_tail_statistics()
    records = after["records"] - before["records"]
    assert 0 < records <= nodes
    assert (after["record_bytes"] - before["record_bytes"]) / records <= 400


# ---------------------------------------------------------------------------
# (c) production の consumer
# ---------------------------------------------------------------------------


def test_explicit_arguments_with_one_target_but_different_values_are_not_collapsed(monkeypatch):
    # 1 つの callee の引数に、同じ parameter の別の piece が 2 つ来た: 値が違うので 1 つに潰さない
    from scripts.function_tracer_pcode.analysis.effects import call_argument

    monkeypatch.setattr(call_argument, "_expression_maps_to_parameter", lambda expr, params: True)
    sentinel = [object()]
    monkeypatch.setattr(
        call_argument, "_select_explicit_call_arguments_by_input_storage", lambda *args, **kwargs: sentinel,
    )
    low, high = publish(_subpiece(0)), publish(_subpiece(4))
    chosen = call_argument._impl__select_aligned_explicit_call_arguments(
        None, None, [{"name": "param_1", "index": 0}], [{"name": "a", "index": 0}], [low, high],
    )
    assert chosen is sentinel
    # 対照: 同じ値の 2 つは従来どおり 1 つに潰す
    again = publish(_subpiece(0))
    chosen = call_argument._impl__select_aligned_explicit_call_arguments(
        None, None, [{"name": "param_1", "index": 0}], [{"name": "a", "index": 0}], [low, again],
    )
    assert chosen == [low]


def test_call_effect_argument_keys_keep_values_with_one_target_apart():
    from scripts.function_tracer_pcode.proof.call_effect.obligations import _dedupe, _expression_key

    zext, sext = publish(_extend("INT_ZEXT")), publish(_extend("INT_SEXT"))
    groups = _dedupe([(_expression_key(zext),), (_expression_key(sext),)])
    # 2 つの証拠が別の値を渡す: 引数の組は 1 つに決まらない（extraction_complete にしない）
    assert len(groups) == 2


def test_the_cross_side_shape_keeps_the_parameter_index_of_a_value():
    # 値の identity の PARAMETER の label は ("parameter", 名前, ("int", index), 大きさ): 形は index を持つ
    from scripts.function_tracer_pcode.proof.call_effect.obligations import _cross_binary_expression_shape

    first = _cross_binary_expression_shape(value_identity(Expression.parameter("a", 0, "int", size=4)))
    second = _cross_binary_expression_shape(value_identity(Expression.parameter("b", 1, "int", size=4)))
    assert first != second
    assert first == ("expression", ("parameter", 0, 4))
    # 旧 provenance key の ref の形は従来どおり
    ref_key = object_target_key(_param(ref=_param_ref(2, 11)))
    assert _cross_binary_expression_shape(ref_key) == ("runtime_ref", ("parameter", 2))


def test_cross_side_comparisons_never_identify_through_a_side_local_token():
    # 超予算の値の exact identity は 1 つの解析の中の identity: 左右の比較では一致に使わない
    from scripts.function_tracer_pcode.proof.call_effect.obligations import _cross_binary_expression_shape
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    left = value_identity(_deep_chain(Expression.parameter("p", 0, "int", size=4), 400))
    right = value_identity(_deep_chain(Expression.parameter("p", 0, "int", size=4), 400))
    assert left == right  # 片側の中では同じ値
    assert _cross_binary_expression_shape(left) != _cross_binary_expression_shape(right)
    component = PairwiseStrategy._cross_binary_call_effect_component_key
    assert component(("argument", left)) != component(("argument", right))
    # 対照: 予算内の値は左右で従来どおり比べる
    small = value_identity(Expression.constant(3, size=4))
    assert component(("argument", small)) == component(("argument", value_identity(Expression.constant(3, size=4))))


def test_label_view_reads_identity_atoms_inside_value_and_target_keys():
    key = object_target_key(_param(ref=_param_ref(2, 1234)))
    assert label_view(key) == ("runtime_ref", ("parameter", 1234, 0x100, 2))
    value = value_identity(Expression.binary_op("INT_ADD", _unknown(4), Expression.constant(1, size=4)))
    viewed = label_view(value)
    assert viewed[0] == "expression"


def test_the_rewrite_match_tells_apart_operands_that_differ_only_in_width():
    # 描画した SMT の文字列は PARAMETER の幅を持たない（`param_1` の 4 byte と 8 byte が同じ文字列）。
    # 文字列の一致で「同じ operand」とすると、最小の差分の探索が幅の違いを飛ばし、別の operand の
    # 等しさだけを証明して書き換え全体を証明済みにする
    from scripts.function_tracer_pcode.proof.strategies import pairwise_solver_proven_rewrite as rewrite

    narrow = publish(Expression.parameter("param_1", 0, "int", size=4))
    wide = publish(Expression.parameter("param_1", 0, "int", size=8))
    assert narrow.to_smt() == wide.to_smt()
    assert not rewrite._exprs_match(narrow, wide)
    original = publish(Expression.binary_op("INT_ADD", narrow, Expression.constant(1, size=4)))
    rewritten = publish(Expression.binary_op("INT_ADD", wide, Expression.constant(2, size=4)))
    assert rewrite._extract_minimal_rewrite_difference(original, rewritten) == (original, rewritten)
    # 対照: 1 operand だけ違えば、その operand へ絞る
    same_width = publish(Expression.binary_op("INT_ADD", Expression.parameter("param_1", 0, "int", size=4),
                                              Expression.constant(2, size=4)))
    assert rewrite._extract_minimal_rewrite_difference(original, same_width)[0].value == 1


def _guard_case(index, conditions_smt):
    return SimpleNamespace(index=index, conditions=(), get_conditions_smt=lambda renderer: list(conditions_smt))


def test_guard_overlap_nodes_are_keyed_by_exact_queries_and_rendered_conditions(monkeypatch):
    from scripts.function_tracer_pcode.proof.obligations import guard_overlap

    monkeypatch.setattr(guard_overlap, "canonical_guard_query_digest", lambda query: "0" * 64)
    monkeypatch.setattr(structural.hashlib, "sha256", _ConstantSha)
    graph = guard_overlap.GuardOverlapGraph(("view",), "premise")
    left = guard_overlap.guard_seed("left", _guard_case(0, ["(bvslt a b)"]), None)
    right = guard_overlap.guard_seed("right", _guard_case(0, ["(bvslt b a)"]), None)
    other_right = guard_overlap.guard_seed("right", _guard_case(0, ["(bvsle b a)"]), None)
    one = graph.requirement(left, right, "(assert (bvslt a b))\n(check-sat)")
    two = graph.requirement(left, right, "(assert (bvsle a b))\n(check-sat)")
    three = graph.requirement(left, other_right, "(assert (bvslt a b))\n(check-sat)")
    assert one.canonical_query_digest == two.canonical_query_digest
    assert one.stable_key() != two.stable_key()
    assert one.stable_key() != three.stable_key()
    # 対照: 同じ query・同じ条件は同じ node（comment と空白の違いは同じ query）
    again = graph.requirement(left, right, "; note\n(assert  (bvslt a b))\n(check-sat)")
    assert again.stable_key() == one.stable_key()


def test_the_exact_query_attempt_cache_does_not_answer_another_query_with_the_same_digest(monkeypatch):
    from scripts.function_tracer_pcode.proof.obligations import AttemptCache
    from scripts.function_tracer_pcode.proof.strategies import pairwise_query_executor as executor

    calls = []

    class _Runner:
        timeout = 1

        def run(self, query, timeout=None):
            calls.append(query)
            return SimpleNamespace(
                is_equivalent=True, results=(SimpleNamespace(elapsed_time=0.0, solver_name="z3", status="unsat",
                                                             error_message=None),),
                get_counterexample=lambda: None,
            )

    monkeypatch.setattr(executor.hashlib, "sha256", _ConstantSha)
    monkeypatch.setattr(executor, "_run_query_with_timeout", lambda runner, query, timeout: runner.run(query))
    monkeypatch.setattr(executor, "_log_solver_errors", lambda *args: None)
    monkeypatch.setattr(
        executor.SolverQueryExecutionReceipt, "from_execution", classmethod(lambda cls, **kwargs: None),
    )
    strategy = SimpleNamespace(
        per_query_timeout=1, per_query_timeout_hard=1, solver_runner=_Runner(),
        _exact_query_attempt_cache=AttemptCache(), _debug_print=lambda *args: None,
        save_unknown_queries=False,
    )
    executor.solve_query_internal(strategy, "(assert true)\n(check-sat)", "p")
    executor.solve_query_internal(strategy, "(assert false)\n(check-sat)", "p")
    assert len(calls) == 2
    # 対照: 同じ query は cache から答える
    executor.solve_query_internal(strategy, "(assert false)\n(check-sat)", "p")
    assert len(calls) == 2


def test_an_expression_without_a_digest_gives_its_evidence_no_fingerprint():
    # 旧 `__json_identity__` は digest の無い式をすべて "None" にし、別の式の証拠が同じ fingerprint になった
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget, RESULT_JSON_POLICY, _OpaqueLeaf

    class _Object:
        pass

    left, right = Expression.constant(0, size=4), Expression.constant(0, size=4)
    left.value, right.value = _Object(), _Object()
    assert structural.structural_identity_digest(publish(left)) is None
    for expr in (left, right):
        with pytest.raises(_OpaqueLeaf):
            RESULT_JSON_POLICY.token_fingerprint({"value": publish(expr)}, work=JsonBudget(1 << 20))
    # 対照: digest のある式は fingerprint を持ち、同じ値なら同じ
    one = RESULT_JSON_POLICY.token_fingerprint({"value": publish(Expression.constant(1, size=4))}, work=JsonBudget(1 << 20))
    two = RESULT_JSON_POLICY.token_fingerprint({"value": publish(Expression.constant(1, size=4))}, work=JsonBudget(1 << 20))
    assert one == two


def _readonly_query(seed_kwargs, case):
    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
        ABI_WIDTH_READONLY_REASON_REGISTRY,
        ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        AbiWidthReadonlyBlockerSignal,
        AbiWidthReadonlyPilotEncoder,
        AbiWidthReadonlySolverQueryAuthority,
        ResolvedReadonlyObjectSetSeed,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import ProductionDualWritePilotConnector
    from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_abi_width_readonly import (
        _readonly_seed,
    )

    session = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=AbiWidthReadonlyPilotEncoder(),
    ).begin({"case": case})
    resolved = ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
        session, _readonly_seed(identified=True, **seed_kwargs), (),
    )
    blocker = AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(resolved)
    assert session.emit_domain_signal(blocker) == 1
    return AbiWidthReadonlySolverQueryAuthority.from_readonly_correspondence_theorem(session, blocker, resolved)


def test_readonly_value_symbols_are_not_shared_by_a_digest_collision(monkeypatch):
    # 左右の readonly の値の記号は、値の key が同じときだけ共有する。key の digest が衝突しても別の値は
    # 別の記号（共有すると near miss（側ごとの storage の値）が UNSAT になり、誤った EQ の根拠になる）
    from scripts.function_tracer_pcode.authority.domains import abi_width_readonly
    from scripts.function_tracer_pcode.smt.interface import SolverStatus
    from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver

    real = abi_width_readonly.authority_digest

    def colliding(value):
        if type(value) is tuple and value and value[0] in {
            "side_local_readonly_value_v2", "shared_parameter_memory_value_v2",
        }:
            return "0" * 64
        return real(value)

    monkeypatch.setattr(abi_width_readonly, "authority_digest", colliding)
    solver = Z3Solver(timeout=5)
    available, message = solver.check_availability()
    assert available, message
    near_miss = _readonly_query({"pointer_kind": "storage"}, "pr-d-near-miss")
    assert solver.check_equivalence_direct(near_miss.query_text).status is SolverStatus.SAT
    # 対照: 同じ parameter の memory を読む組は共有して UNSAT のまま
    positive = _readonly_query({"right_pointer_index": 0}, "pr-d-positive")
    assert solver.check_equivalence_direct(positive.query_text).status is SolverStatus.UNSAT


def test_extension_evidence_requires_the_same_payload_value_not_only_the_same_target():
    # 戻り値の幅の拡張の証拠: certificate が名指す payload と、式の拡張の operand が同じ **値** のときだけ
    # 使う。同じ parameter の別の piece（同じ対象・別の値）を certificate が名指しても受け入れない
    from scripts.function_tracer_pcode.core import ReturnValueFlowCertificate
    from scripts.function_tracer_pcode.proof.return_width.surface import extract_function_return_width_seed
    from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import extract_return_cases
    from scripts.function_tracer_pcode.tests.unit.test_return_width_surface import _analysis

    def seed_for(claimed_payload):
        analysis = _analysis("B-pr-d", 0x1900, 64, extension="INT_ZEXT")
        payload = publish(_subpiece(0))
        extended = Expression.unary_op("INT_ZEXT", payload)
        extended.size = 8
        analysis.returns[0].value = publish(extended)
        certificate = analysis.returns[0].return_value_flow_certificate
        analysis.returns[0].return_value_flow_certificate = ReturnValueFlowCertificate(
            return_op_ref=certificate.return_op_ref,
            return_input_index=certificate.return_input_index,
            return_input_ref=certificate.return_input_ref,
            steps=certificate.steps,
            extension_step_index=certificate.extension_step_index,
            payload_expression_identity=tuple(value_identity(publish(claimed_payload))),
        )
        return extract_function_return_width_seed(analysis, extract_return_cases(analysis)[0])

    assert object_target_key(publish(_subpiece(0))) == object_target_key(publish(_subpiece(4)))
    accepted = seed_for(_subpiece(0))
    rejected = seed_for(_subpiece(4))
    assert accepted.extension_evidence_source.kind == "zero_extend"
    assert rejected.extension_evidence_source.kind != "zero_extend" or not rejected.complete
