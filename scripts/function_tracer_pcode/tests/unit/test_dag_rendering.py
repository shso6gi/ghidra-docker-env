# -*- coding: utf-8 -*-
"""DAG-aware な描画（Issue #22 / PR-22-C）の AC C1〜C7。

* **C1** old（展開）と new（`let` 共有）の **意味一致** を solver で確かめる。
  「両方 SAT だった」ではなく **差分式が UNSAT** であることを見る。
  UNKNOWN / timeout は pass にしない。
* **C2** 共有 DAG（深さ 40）と深い線形式（深さ 10,000）。
* **C3** 束縛名の衝突回避と、上限到達時の typed limitation。
* **C4** 描画文脈が違う同じ node を同じ束縛に混ぜない。
* **C5** 人向け表示の決定性と共有参照。
* **C6** `to_string()` を identity に使っていない。
* **C7** `CountingWriter` が上限で止まり、完成文字列を作らない。
"""

from __future__ import annotations

import importlib
import sys

import pytest

from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.render_metrics import (
    render_metrics_snapshot,
    reset_render_metrics,
)
from scripts.function_tracer_pcode.core.render_output import (
    CountingWriter,
    RenderCounters,
    RenderOutputLimitExceeded,
)
from scripts.function_tracer_pcode.core.render_plan import (
    TEXT_OBSERVATION_OTHER,
    BindingNamespace,
    SharingPolicy,
    TextObservation,
    plan_render,
)
from scripts.function_tracer_pcode.core.render_python import expression_to_string
from scripts.function_tracer_pcode.core.render_smt import _to_smt_internal
from scripts.function_tracer_pcode.core.render_smt.attributes import iter_expression_nodes
from scripts.function_tracer_pcode.core.render_smt.bindings import (
    SMT_BINDING_PREFIX,
    binding_dependency_order_is_valid,
    rendered_binding_names,
)
from scripts.function_tracer_pcode.core.render_smt.render import (
    expression_returns_bool,
    render_smt_term,
)
from scripts.function_tracer_pcode.core.render_smt.context import build_smt_render_context
from scripts.function_tracer_pcode.core.render_smt.unknowns import (
    collect_unknown_smt_declarations,
)
from scripts.function_tracer_pcode.core.render_smt.widths import expression_smt_bit_width
from scripts.function_tracer_pcode.core.runtime_refs.locations import AddressValueRef
from scripts.function_tracer_pcode.core.semantic_freeze import publish


# ---------------------------------------------------------------------------
# 式の組み立て
# ---------------------------------------------------------------------------


def _param(name: str, index: int = 0, size: int = 4) -> Expression:
    return Expression.parameter(name, index, size=size)


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size=size)


def _variable(name: str, size: int = 4, runtime_ref=None) -> Expression:
    return Expression(ExpressionType.VARIABLE, name=name, size=size, runtime_ref=runtime_ref)


def _binary(operator: str, left, right, size: int = 4) -> Expression:
    expr = Expression.binary_op(operator, left, right)
    expr.size = size
    return expr


def _unary(operator: str, operand, size: int = 4) -> Expression:
    expr = Expression.unary_op(operator, operand)
    expr.size = size
    return expr


def _doubling_dag(depth: int, leaf: Expression) -> Expression:
    """同じ部分式を 2 回ずつ使う DAG。木に戻すと 2**depth の葉になる。"""

    node = leaf
    for _ in range(depth):
        node = _binary("INT_ADD", node, node)
    return node


def _linear_chain(depth: int, leaf: Expression) -> Expression:
    node = leaf
    step = _const(1)
    for _ in range(depth):
        node = _binary("INT_ADD", node, step)
    return node


# ---------------------------------------------------------------------------
# solver による意味一致の確認
# ---------------------------------------------------------------------------


def _z3():
    """z3 の Python module。**無いときは skip ではなく fail**。

    old / new の意味一致は本 PR の中心的な主張なので、solver が無いまま緑に
    しない（記録 corpus の replay と同じ立場）。
    """

    try:
        return importlib.import_module("z3")
    except ImportError as exc:  # pragma: no cover - 環境不備の明示
        pytest.fail(f"z3 python module is required for the differential check: {exc}")


def _declaration_lines(expr) -> list:
    """test 用の宣言。式に出てくる自由 symbol をすべて宣言する。"""

    lines = []
    declared = set()

    def declare(name: str, sort: str) -> None:
        if name in declared:
            return
        declared.add(name)
        lines.append(f"(declare-const {name} {sort})")

    for name, bits in collect_unknown_smt_declarations(expr):
        declare(name, f"(_ BitVec {int(bits)})")

    for node in iter_expression_nodes(expr):
        expr_type = getattr(node, "expr_type", None)
        if expr_type is None:
            continue
        bits = max(1, int(expression_smt_bit_width(node) or 1))
        if expr_type == ExpressionType.PARAMETER:
            declare(node.name or f"param_{node.value}", f"(_ BitVec {bits})")
        elif expr_type == ExpressionType.VARIABLE:
            rendered = _to_smt_internal(node)
            if rendered.isidentifier() or rendered == (node.name or "var"):
                declare(rendered, f"(_ BitVec {bits})")
        elif expr_type == ExpressionType.MEMORY:
            mem_bits = bits if bits in (8, 16, 32, 64) else 32
            declare(
                f"mem{mem_bits}",
                f"(Array (_ BitVec 64) (_ BitVec {mem_bits}))",
            )
    return lines


def _assert_same_meaning(expr, *, float_mode: str = "uf") -> None:
    """展開した描画と `let` 共有の描画の **差分式が UNSAT** であることを見る。"""

    z3 = _z3()
    inline = _to_smt_internal(expr, float_mode=float_mode, shared=False)
    shared = _to_smt_internal(expr, float_mode=float_mode, shared=True)
    if inline == shared:
        # 共有が働かなかった式（小さい式）。文字列一致は意味一致より強い。
        return
    if expression_returns_bool(expr):
        difference = f"(assert (xor {inline} {shared}))"
    else:
        difference = f"(assert (distinct {inline} {shared}))"
    script = "\n".join(_declaration_lines(expr) + [difference])
    solver = z3.Solver()
    solver.set("timeout", 30000)
    solver.add(z3.parse_smt2_string(script))
    verdict = solver.check()
    assert verdict == z3.unsat, (
        f"shared rendering is not equivalent to the inline rendering: {verdict}\n{script[:2000]}"
    )


def _differential_corpus():
    a = _param("a", 0)
    b = _param("b", 1)
    wide = _param("w", 2, size=8)
    narrow = _param("n", 3, size=1)
    shared_sum = _binary("INT_ADD", a, b)
    memory = Expression(ExpressionType.MEMORY, operands=[wide], size=4)
    condition = Condition(_binary("INT_LESS", a, b, size=1))
    phi = Expression.phi([(condition, shared_sum), (None, _binary("INT_MULT", a, a))])
    phi.size = 4
    return {
        "doubling_dag_depth_12": _doubling_dag(12, a),
        "shared_operands": _binary(
            "INT_MULT",
            _doubling_dag(6, shared_sum),
            _doubling_dag(6, shared_sum),
        ),
        "mixed_operators": _binary(
            "INT_XOR",
            _binary("INT_LEFT", _doubling_dag(5, a), _const(3)),
            _binary("INT_AND", _doubling_dag(5, b), _const(0xFF)),
        ),
        "width_mixing": _binary(
            "INT_ADD",
            _unary("INT_SEXT", _doubling_dag(5, narrow), size=4),
            _unary("INT_ZEXT", _doubling_dag(5, narrow), size=4),
        ),
        "memory_select": _binary("INT_ADD", _doubling_dag(6, memory), _doubling_dag(6, a)),
        "phi_with_condition": _doubling_dag(6, phi),
        "boolean_root": _binary(
            "INT_LESS",
            _doubling_dag(6, a),
            _doubling_dag(6, b),
            size=1,
        ),
    }


@pytest.mark.parametrize("case", sorted(_differential_corpus()))
def test_c1_shared_rendering_has_the_same_meaning(case):
    """C1: old / new の差分式が UNSAT。SAT / UNKNOWN / timeout は失敗。"""

    _assert_same_meaning(_differential_corpus()[case])


def test_c1_doubling_dag_matches_an_independent_algebraic_oracle():
    """C1 / C2: 巨大な old 文字列を作らず、独立した期待式と比べる。

    `a` を 40 回自分自身と足したものは `a * 2**40`（32 bit で切り捨て）。
    """

    z3 = _z3()
    a = _param("a", 0)
    rendered = _to_smt_internal(_doubling_dag(40, a))
    multiplier = (1 << 40) % (1 << 32)
    oracle = f"(bvmul a (_ bv{multiplier} 32))"
    script = "\n".join(
        [
            "(declare-const a (_ BitVec 32))",
            f"(assert (distinct {rendered} {oracle}))",
        ]
    )
    solver = z3.Solver()
    solver.set("timeout", 30000)
    solver.add(z3.parse_smt2_string(script))
    assert solver.check() == z3.unsat


# ---------------------------------------------------------------------------
# C2: 共有 DAG と深い線形式
# ---------------------------------------------------------------------------


def test_c2_shared_dag_visits_distinct_nodes_only():
    a = _param("a", 0)
    root = _doubling_dag(40, a)
    reset_render_metrics()
    rendered = _to_smt_internal(root)
    metrics = render_metrics_snapshot()

    # distinct node は葉 + 40 段。木に戻すと 2**40 node になる。
    assert metrics["distinct_rendered_nodes"] == 41
    assert metrics["tree_node_estimate"] > (1 << 39)
    assert len(rendered) < 4000
    # 名前を付けるのは「展開したままだと大きい」段だけなので、段数より少ない。
    assert 10 <= metrics["shared_bindings"] <= 41
    assert metrics["shared_references"] >= metrics["shared_bindings"]


def test_c2_shared_dag_output_grows_linearly_with_depth():
    a = _param("a", 0)
    sizes = [len(_to_smt_internal(_doubling_dag(depth, a))) for depth in (20, 40, 80)]
    # 木に戻すと 2**depth。共有していれば深さ 4 倍で概ね 4 倍に収まる。
    assert sizes[2] < 8 * sizes[0]
    assert sizes[2] < 20000


def test_c2_deep_linear_expression_renders_without_python_recursion():
    limit_before = sys.getrecursionlimit()
    a = _param("a", 0)
    root = _linear_chain(10000, a)

    smt = _to_smt_internal(root)
    human = expression_to_string(root)

    assert sys.getrecursionlimit() == limit_before, "recursion limit must not be raised to pass"
    assert smt.count("bvadd") >= 10000
    assert "+" in human
    assert len(smt) < 400000


def test_c2_rendering_is_deterministic_for_the_same_graph():
    a = _param("a", 0)
    root = _doubling_dag(30, a)
    first = _to_smt_internal(root)
    assert all(_to_smt_internal(root) == first for _ in range(3))

    # object の同一性ではなく形から決まること（別 object の同型 graph）。
    twin = _doubling_dag(30, _param("a", 0))
    assert _to_smt_internal(twin) == first

    human_first = expression_to_string(root)
    assert expression_to_string(root) == human_first
    assert expression_to_string(twin) == human_first


def test_c2_binding_dependency_order_is_nested_and_acyclic():
    a = _param("a", 0)
    rendered = _to_smt_internal(_doubling_dag(20, a))
    names = rendered_binding_names(rendered)
    assert names
    # 入れ子の `let` なので、束縛名は定義された後にしか現れない。
    for position, name in enumerate(names):
        definition = rendered.index(f"(let (({name} ")
        first_use = rendered.index(name, definition + len(name) + 8)
        assert first_use > definition
        if position:
            assert rendered.index(f"(let (({name} ") > rendered.index(
                f"(let (({names[position - 1]} "
            )


# ---------------------------------------------------------------------------
# C3: 名前空間の衝突と上限
# ---------------------------------------------------------------------------


def test_c3_generated_bindings_do_not_capture_program_symbols():
    """program 由来の symbol が生成名と同じ綴りでも捕まえない。"""

    colliding = _variable("?sh_0", size=4)
    root = _doubling_dag(20, _binary("INT_ADD", colliding, _param("a", 0)))
    rendered = _to_smt_internal(root)

    assert "?sh_0" in rendered  # program symbol はそのまま出る
    names = rendered_binding_names(rendered)
    assert names
    assert all(name != "|?sh_0|" for name in names)
    _assert_same_meaning(root)


def test_c3_binding_namespace_probes_deterministically():
    reserved = {f"?sh_{index}" for index in range(4)}
    namespace = BindingNamespace(reserved, prefix="?sh", template="|{prefix}_{index}|")
    first = namespace.allocate(4)
    assert first == namespace.allocate(4)
    assert all(name[1:-1] not in reserved for name in first)


def test_c3_output_limit_raises_a_typed_limitation():
    a = _param("a", 0)
    root = _doubling_dag(20, a)
    context = build_smt_render_context()
    with pytest.raises(RenderOutputLimitExceeded) as excinfo:
        render_smt_term(root, context, None, limit_chars=64)
    assert excinfo.value.limit_chars == 64
    assert excinfo.value.site == "core.render_smt"


def test_c3_no_recursive_tree_fallback_remains_in_the_renderer():
    """描画本体から入口へ戻る再帰が残っていないこと。

    無制限の tree fallback は「共有できなかったら木に戻す」経路で、これが
    あると深い式・共有の多い式で元の問題に戻る。
    """

    import ast
    import pathlib

    render_dir = pathlib.Path(
        importlib.import_module("scripts.function_tracer_pcode.core.render_smt").__file__
    ).parent
    # `unknowns.py` は宣言名を作るために VARIABLE（葉）1 個を描く。node 本体
    # から子を描く経路ではないので、driver を経由しなくても再帰にならない。
    allowed = {"unknowns.py"}
    offenders = []
    for path in sorted(render_dir.glob("*.py")):
        if path.name in {"__init__.py", "render.py"} or path.name in allowed:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                if node.func.id in {"_to_smt_internal", "expression_to_smt"}:
                    offenders.append(f"{path.name}:{node.lineno}")
    assert offenders == [], f"renderer helpers must render children through render_child: {offenders}"


# ---------------------------------------------------------------------------
# C4: 描画文脈ごとの共有
# ---------------------------------------------------------------------------


def test_c4_same_node_in_two_contexts_gets_two_bindings():
    """address 文脈と通常文脈では同じ node でも描画が違う → 別の束縛。"""

    ref = AddressValueRef(address_offset=0x2000, source="ghidra_object")
    global_variable = _variable("g", size=8, runtime_ref=ref)
    address_use = _doubling_dag(
        20, Expression(ExpressionType.MEMORY, operands=[global_variable], size=4)
    )
    value_use = _doubling_dag(20, _unary("INT_ZEXT", global_variable, size=4))
    root = _binary("INT_ADD", address_use, value_use)

    rendered = _to_smt_internal(root)
    # address 文脈では定数へ、通常文脈では symbol のまま。両方が出ている。
    assert "(_ bv8192 64)" in rendered
    assert " g)" in rendered or "(g" in rendered or " g " in rendered
    _assert_same_meaning(root)


def test_c4_render_plan_keys_instances_by_node_and_context():
    """共有 key が node identity だけになっていないこと（plan 層の契約）。"""

    node = object()
    root = ("root", node)
    observations = (
        TextObservation(
            name=TEXT_OBSERVATION_OTHER,
            matches=lambda text: True,
            token=lambda index: f"t{index}",
        ),
    )

    def body(current, context, resolve):
        if current is root:
            return f"[{resolve(node, 'wide')}|{resolve(node, 'narrow')}]"
        return f"<{context}>"

    plan = plan_render(
        root,
        "root-context",
        body=body,
        observations=observations,
        policy=SharingPolicy(min_shared_chars=0, min_shared_tree_nodes=1),
        counters=RenderCounters(),
    )
    contexts = {instance.context for instance in plan.instances if instance.node is node}
    assert contexts == {"wide", "narrow"}
    assert len({instance.index for instance in plan.instances if instance.node is node}) == 2


# ---------------------------------------------------------------------------
# C5: 人向け表示
# ---------------------------------------------------------------------------


def test_c5_human_rendering_uses_shared_references_instead_of_re_expansion():
    a = _param("a", 0)
    root = _doubling_dag(40, a)
    reset_render_metrics()
    text = expression_to_string(root)
    metrics = render_metrics_snapshot()

    assert " where " in text
    assert "@h" in text
    assert len(text) < 20000
    assert metrics["distinct_rendered_nodes"] == 41
    assert metrics["shared_bindings"] >= 1


def test_c5_small_expressions_keep_their_existing_text():
    a = _param("a", 0)
    b = _param("b", 1)
    assert expression_to_string(_binary("INT_ADD", a, b)) == "(a + b)"
    assert " where " not in expression_to_string(_doubling_dag(3, a))


def test_c5_human_shared_reference_names_are_stable_and_collision_free():
    a = _param("a", 0)
    root = _doubling_dag(40, a)
    first = expression_to_string(root)
    assert expression_to_string(root) == first

    # program 由来の名前とぶつかっても捕まえない。
    reference = first.split(" where ")[1].split(" = ")[0]
    colliding = _variable(reference, size=4)
    mixed = _binary("INT_ADD", _doubling_dag(40, colliding), colliding)
    text = expression_to_string(mixed)
    definitions = [part.split(" = ")[0] for part in text.split(" where ")[1].split("; ")]
    assert reference not in definitions


# ---------------------------------------------------------------------------
# C6: identity に表示文字列を使わない
# ---------------------------------------------------------------------------


def test_c6_condition_identity_does_not_render_text(monkeypatch):
    """identity 計算が `to_string()` を呼ばないこと。"""

    from scripts.function_tracer_pcode.core.structural import condition_key

    def _boom(*_args, **_kwargs):
        raise AssertionError("identity must not depend on the human rendering")

    monkeypatch.setattr(Expression, "to_string", _boom)
    monkeypatch.setattr(Condition, "to_string", _boom)

    condition = Condition(_binary("INT_LESS", _param("a", 0), _param("b", 1), size=1))
    assert condition_key(condition) == condition.structural_key()


def test_c6_identity_sites_no_longer_reference_to_string():
    import pathlib

    package = pathlib.Path(
        importlib.import_module("scripts.function_tracer_pcode").__file__
    ).parent
    sites = {
        package / "analysis" / "returns" / "return_extraction.py": "_return_info_summary_identity_key",
        package / "analysis" / "returns" / "control_recovery.py": "branch_guarded_affine_unit_count_structural_proof",
    }
    for path, marker in sites.items():
        text = path.read_text(encoding="utf-8")
        assert marker in text
        index = text.index(marker)
        window = text[index : index + 2000]
        assert "to_string()" not in window, f"{path.name} still keys identity on rendered text"


def test_c6_structural_identity_dedup_is_unchanged():
    """置換前後で dedup が変わらないこと（同じ条件は同じ key）。"""

    from scripts.function_tracer_pcode.core.structural import condition_key

    left = Condition(_binary("INT_LESS", _param("a", 0), _param("b", 1), size=1))
    right = Condition(_binary("INT_LESS", _param("a", 0), _param("b", 1), size=1))
    other = Condition(_binary("INT_LESS", _param("b", 1), _param("a", 0), size=1))
    assert condition_key(left) == condition_key(right)
    assert condition_key(left) != condition_key(other)


# ---------------------------------------------------------------------------
# C7: CountingWriter
# ---------------------------------------------------------------------------


def test_c7_counting_writer_stops_at_the_limit_without_building_the_string():
    writer = CountingWriter(limit_chars=10, site="test")
    writer.write("12345")
    assert writer.emitted_chars == 5
    assert writer.peak_buffered_chars == 5
    with pytest.raises(RenderOutputLimitExceeded):
        writer.write("678901")
    assert writer.aborted is True
    assert writer.getvalue() == ""
    assert writer.emitted_chars <= 10


def test_c7_counting_writer_without_limit_joins_once():
    writer = CountingWriter()
    for part in ("a", "b", "c"):
        writer.write(part)
    assert writer.getvalue() == "abc"
    assert writer.emitted_chars == 3
    assert writer.part_count == 3


def test_c7_counters_are_diagnostic_only():
    """counter は判定を変えない: 同じ式は counter を消しても同じ text。"""

    a = _param("a", 0)
    root = _doubling_dag(12, a)
    reset_render_metrics()
    first = _to_smt_internal(root)
    before = render_metrics_snapshot()
    second = _to_smt_internal(root)
    after = render_metrics_snapshot()
    assert first == second
    assert after["render_invocations"] > before["render_invocations"]


def test_c7_metrics_accumulate_and_reset():
    reset_render_metrics()
    assert render_metrics_snapshot()["render_invocations"] == 0
    _to_smt_internal(_binary("INT_ADD", _param("a", 0), _param("b", 1)))
    assert render_metrics_snapshot()["render_invocations"] == 1
    reset_render_metrics()
    assert render_metrics_snapshot()["render_invocations"] == 0


# ---------------------------------------------------------------------------
# 既存の観測可能な出力との互換
# ---------------------------------------------------------------------------


def test_small_terms_are_byte_identical_with_and_without_sharing():
    a = _param("a", 0)
    b = _param("b", 1)
    for expr in (
        _binary("INT_ADD", a, b),
        _binary("INT_MULT", _binary("INT_ADD", a, b), _const(3)),
        _doubling_dag(3, a),
    ):
        assert _to_smt_internal(expr, shared=True) == _to_smt_internal(expr, shared=False)


def test_published_solver_entry_still_requires_publication():
    from scripts.function_tracer_pcode.core.render_smt import expression_to_smt
    from scripts.function_tracer_pcode.core.errors import UnpublishedSemanticInputError

    expr = _binary("INT_ADD", _param("a", 0), _param("b", 1))
    with pytest.raises(UnpublishedSemanticInputError):
        expression_to_smt(expr)
    publish(expr)
    assert expression_to_smt(expr) == "(bvadd a b)"


def test_binding_dependency_contract_holds_for_a_large_dag():
    from scripts.function_tracer_pcode.core.render_plan import emit_render, plan_render
    from scripts.function_tracer_pcode.core.render_smt.bindings import (
        SMT_SHARING_POLICY,
        assign_binding_names,
        smt_binding_namespace,
    )
    from scripts.function_tracer_pcode.core.render_smt.render import (
        _SMT_TEXT_OBSERVATIONS,
        _render_smt_node,
    )

    a = _param("a", 0)
    root = _doubling_dag(24, a)
    counters = RenderCounters()
    context = build_smt_render_context()

    def body(node, node_context, resolve):
        return _render_smt_node(node, node_context, resolve, None, counters)

    plan = plan_render(
        root,
        context,
        body=body,
        observations=_SMT_TEXT_OBSERVATIONS,
        policy=SMT_SHARING_POLICY,
        counters=counters,
    )
    namespace = smt_binding_namespace(instance.planned_text for instance in plan.instances)
    names = assign_binding_names(plan, namespace)
    emit_render(plan, root, context, body=body, names=names, counters=counters)

    assert names
    assert all(name.startswith(f"|{SMT_BINDING_PREFIX}") for name in names.values())
    assert binding_dependency_order_is_valid(plan, names)
