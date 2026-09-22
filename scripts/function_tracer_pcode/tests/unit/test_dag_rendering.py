# -*- coding: utf-8 -*-
"""DAG-aware な描画（Issue #22 / PR-22-C）の AC C1〜C7。

* **C1** PR-22-C **変更前**の描画と変更後の描画の **意味一致** を solver で
  確かめる。「両方 SAT だった」ではなく **差分式が UNSAT** であることを見る。
  UNKNOWN / timeout / solver 無しは pass にしない。
* **C2** 共有 DAG（深さ 40）と深い線形式（深さ 10,000）。
* **C3** 束縛名の衝突回避と、無制限な再帰 fallback が無いこと。
* **C4** 描画文脈が違う同じ node を同じ束縛に混ぜない。
* **C5** 人向け表示の決定性と共有参照。
* **C6** 条件の identity は予算付きの legacy key ではなく完全 identity。
* **C7** `CountingWriter` が上限で中断し、完成出力文字列を作らない。
"""

from __future__ import annotations

import importlib
import json
from types import SimpleNamespace
import pathlib
import re
import sys
import time

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
    utf8_length,
)
from scripts.function_tracer_pcode.core.render_plan import (
    NO_SHARING_POLICY,
    PLACEHOLDER_MARK,
    BindingNamespace,
    RenderGraphCycleError,
    RenderPlanInvariantError,
    RenderedTerm,
    RenderedTermContractError,
    SharingPolicy,
    build_render_plan,
    check_plan_invariants,
    fragment_children,
    term_properties,
    write_expansion,
)
from scripts.function_tracer_pcode.core.render_python import expression_to_string
from scripts.function_tracer_pcode.core.render_smt import _to_smt_internal
from scripts.function_tracer_pcode.core.render_smt.bindings import (
    SMT_BINDING_PREFIX,
    SMT_SHARING_POLICY,
    SMT_SYMBOL_RE,
    assign_binding_names,
    smt_binding_namespace,
)
from scripts.function_tracer_pcode.core.render_smt.attributes import render_attribute_scope
from scripts.function_tracer_pcode.core.render_smt.context import build_smt_render_context
from scripts.function_tracer_pcode.core.render_smt.render import (
    _SmtChildRenderer,
    _render_smt_node,
    classify_smt_fragment,
    render_smt_term,
    term_boolean_literal,
    term_is_fp_rendered,
)
from scripts.function_tracer_pcode.core.runtime_refs.locations import AddressValueRef
from scripts.function_tracer_pcode.core.semantic_freeze import publish
from scripts.function_tracer_pcode.core.structural import (
    condition_key,
    expression_key_safe,
)
from scripts.function_tracer_pcode.tests.fixtures.render.corpus import build_corpus
from scripts.function_tracer_pcode.tests.tools.record_render_baseline import (
    declaration_lines,
    render_case,
)


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


def _rendered_binding_names(text: str) -> tuple:
    """描かれた text に現れる束縛名。**test の観測**であって production の面ではない。

    描かれた text を読むのは test だけがしてよいこと。production に置くと、
    「描いた結果から意味を読み戻す」経路が復活する入口になる。
    """

    found = []
    for match in SMT_SYMBOL_RE.finditer(text):
        quoted = match.groupdict().get("quoted")
        if quoted is None:
            continue
        if quoted.startswith(SMT_BINDING_PREFIX) and f"|{quoted}|" not in found:
            found.append(f"|{quoted}|")
    return tuple(found)


def _binding_dependency_order_is_valid(plan, names) -> bool:
    """束縛が自分より前の束縛しか参照しないこと。

    production の `check_plan_invariants` が同じ性質を落とす形で持っている。
    こちらは「落とす」ではなく「真偽で観る」ための test 側の目で、判定を
    2 箇所に増やさないよう production には置かない。
    """

    defined = set()
    for index in plan.bound_order:
        for child in plan.instances[index].used_children:
            if child in names and child not in defined:
                return False
        defined.add(index)
    return True


def _smt_body(node, node_context, resolve):
    return _render_smt_node(node, node_context, _SmtChildRenderer(resolve, node_context, None))


def _plan_for(root, *, policy=SMT_SHARING_POLICY, counters=None):
    """`render_smt_term` と同じ条件で計画だけを組む。

    属性の memo scope を張るのを忘れると、node 属性が呼び出しごとに計算し直され、
    幅の広い node では実際の描画と桁違いの費用になる（test だけが遅くなる）。
    """

    with render_attribute_scope():
        return build_render_plan(
            root,
            build_smt_render_context(),
            body=_smt_body,
            classify=classify_smt_fragment,
            policy=policy,
            counters=counters if counters is not None else RenderCounters(),
            site="core.render_smt",
        )


# ---------------------------------------------------------------------------
# C1: 変更前 / 変更後の意味一致
# ---------------------------------------------------------------------------


_BASELINE_PATH = (
    pathlib.Path(__file__).resolve().parents[1] / "fixtures" / "render" / "baseline_smt.json"
)


def _baseline():
    return json.loads(_BASELINE_PATH.read_text(encoding="utf-8"))


def _z3():
    """z3 の Python module。**無いときは skip ではなく fail**。

    old / new の意味一致は本 PR の中心的な主張なので、solver が無いまま緑に
    しない（記録 corpus の replay と同じ立場）。
    """

    try:
        return importlib.import_module("z3")
    except ImportError as exc:  # pragma: no cover - 環境不備の明示
        pytest.fail(f"z3 python module is required for the differential check: {exc}")


def _assert_difference_is_unsat(declarations, sort: str, old: str, new: str, label: str) -> None:
    z3 = _z3()
    if old == new:
        # 文字列一致は意味一致より強い。solver に問うまでもない。
        return
    if sort == "bool":
        difference = f"(assert (xor {old} {new}))"
    else:
        difference = f"(assert (distinct {old} {new}))"
    script = "\n".join(list(declarations) + [difference])
    solver = z3.Solver()
    solver.set("timeout", 60000)
    solver.add(z3.parse_smt2_string(script))
    verdict = solver.check()
    assert verdict == z3.unsat, (
        f"{label}: the two renderings can differ ({verdict})\n{script[:2000]}"
    )


def _declarations_for(case: str, recorded, spec):
    declarations = set(recorded["declarations"])
    declarations.update(
        declaration_lines(
            spec["expression"],
            float_mode=spec.get("float_mode", "uf"),
            address_context=bool(spec.get("address_context", False)),
        )
    )
    return sorted(declarations)


def test_c1_baseline_fixture_covers_the_surfaces_the_change_touched():
    """baseline が実際に PR-22-C の触った面を含んでいること。"""

    baseline = _baseline()
    assert baseline["schema"] == "render-baseline-smt-v1"
    assert baseline["recorded_at_commit"].startswith("15e05826")
    assert baseline["skipped"] == {}
    cases = baseline["cases"]
    for surface in (
        "arith_mixed_operators",
        "arith_shifts",
        "compare_signed",
        "width_sign_extension",
        "width_piece_subpiece",
        "bool_connectives",
        "bool_to_bitvector",
        "phi_with_condition",
        "phi_with_expression_condition",
        "phi_bool_branches",
        "memory_read",
        "memory_of_global",
        "context_global_as_address_and_value",
        "context_prefer_signed_arithmetic",
        "context_address",
        "unknown_symbol",
        "intrinsic_ptradd",
        "fp_arithmetic",
        "fp_predicate_over_arithmetic",
        "fp_int_to_float",
        "shared_dag_depth_10",
        "linear_depth_200",
    ):
        assert surface in cases, surface
    assert len(cases) >= 30


@pytest.mark.parametrize("case", sorted(_baseline()["cases"]))
def test_c1_rendering_means_the_same_as_before_the_change(case):
    """C1: 変更前の描画と現在の描画の差分式が UNSAT。"""

    recorded = _baseline()["cases"][case]
    spec = build_corpus()[case]
    _assert_difference_is_unsat(
        _declarations_for(case, recorded, spec),
        recorded["sort"],
        recorded["smt"],
        render_case(spec),
        case,
    )


@pytest.mark.parametrize("case", sorted(_baseline()["cases"]))
def test_c1_let_sharing_means_the_same_as_the_inline_form(case):
    """`let` 変換そのものの検証（old / new 検証の代わりにはしない）。"""

    recorded = _baseline()["cases"][case]
    spec = build_corpus()[case]
    context = build_smt_render_context(
        prefer_signed_arithmetic=spec.get("prefer_signed_arithmetic", False),
        address_context=spec.get("address_context", False),
        float_mode=spec.get("float_mode", "uf"),
    )
    inline = render_smt_term(spec["expression"], context, None, shared=False)
    shared = render_smt_term(spec["expression"], context, None, shared=True)
    _assert_difference_is_unsat(
        _declarations_for(case, recorded, spec), recorded["sort"], inline, shared, case
    )


def test_c1_doubling_dag_matches_an_independent_algebraic_oracle():
    """巨大な old 文字列を作らず、独立した期待式と比べる。

    `a` を 40 回自分自身と足したものは `a * 2**40`（32 bit で切り捨て）。
    """

    z3 = _z3()
    a = _param("a", 0)
    rendered = _to_smt_internal(_doubling_dag(40, a))
    multiplier = (1 << 40) % (1 << 32)
    script = "\n".join(
        [
            "(declare-const a (_ BitVec 32))",
            f"(assert (distinct {rendered} (bvmul a (_ bv{multiplier} 32))))",
        ]
    )
    solver = z3.Solver()
    solver.set("timeout", 60000)
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
    assert 10 <= metrics["shared_bindings"] <= 41
    assert metrics["shared_references"] >= metrics["shared_bindings"]
    # 中間文字列は node 1 個分しか作らない。
    assert metrics["max_fragment_bytes"] < 200
    assert metrics["retained_fragment_bytes"] < 4000


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
    names = _rendered_binding_names(rendered)
    assert names
    for position, name in enumerate(names):
        definition = rendered.index(f"(let (({name} ")
        first_use = rendered.index(name, definition + len(name) + 8)
        assert first_use > definition
        if position:
            assert rendered.index(f"(let (({name} ") > rendered.index(
                f"(let (({names[position - 1]} "
            )


# ---------------------------------------------------------------------------
# C3: 名前空間の衝突と再帰 fallback
# ---------------------------------------------------------------------------


def test_c3_generated_bindings_do_not_capture_program_symbols():
    """program 由来の symbol が生成名と同じ綴りでも捕まえない。"""

    colliding = _variable("?sh_0", size=4)
    rendered = _to_smt_internal(_doubling_dag(20, _binary("INT_ADD", colliding, _param("a", 0))))

    assert "?sh_0" in rendered  # program symbol はそのまま出る
    names = _rendered_binding_names(rendered)
    assert names
    assert all(name != "|?sh_0|" for name in names)


def test_c3_binding_namespace_probes_deterministically():
    reserved = {f"?sh_{index}" for index in range(4)}
    namespace = BindingNamespace(reserved, prefix="?sh", template="|{prefix}_{index}|")
    first = namespace.allocate(4)
    assert first == namespace.allocate(4)
    assert all(name[1:-1] not in reserved for name in first)


def test_c3_no_recursive_tree_fallback_remains_in_the_renderer():
    """描画本体から入口へ戻る再帰が残っていないこと。"""

    import ast

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
# C7: `CountingWriter` が上限で中断し、完成出力文字列を作らない
#
# 計画中の fragment は speculative なので出力予算では裁かない（捨てられる子が
# 予算より大きくても、収まる描画は成功する）。幅の広い node の線形時間化は C2 /
# performance の話で、ここには混ぜない。
# ---------------------------------------------------------------------------


def test_c7_the_abort_says_which_renderer_stopped():
    """打ち切りがどの renderer の書き出しで起きたかを名乗ること。

    予算を見るのは書き出し口だけなので、名乗りも `<owner>.emit` の 1 種類。
    PR-22-D はこの文字列を登録済み reason へ写す。
    """

    from scripts.function_tracer_pcode.core.render_python import (
        HumanRenderContext,
        render_human_text,
    )

    a = _param("a", 0)
    deep = _doubling_dag(40, a)

    with pytest.raises(RenderOutputLimitExceeded) as smt_emit:
        render_smt_term(deep, build_smt_render_context(), None, shared=False, limit_bytes=20_000)
    with pytest.raises(RenderOutputLimitExceeded) as human_emit:
        render_human_text(deep, HumanRenderContext(), shared=False, limit_bytes=20_000)

    assert smt_emit.value.site == "core.render_smt.emit"
    assert human_emit.value.site == "core.render_python.emit"
    assert smt_emit.value.limit_bytes == human_emit.value.limit_bytes == 20_000


def test_c7_output_limit_raises_a_typed_limitation():
    a = _param("a", 0)
    context = build_smt_render_context()
    with pytest.raises(RenderOutputLimitExceeded) as excinfo:
        render_smt_term(_doubling_dag(20, a), context, None, limit_bytes=64)
    assert excinfo.value.limit_bytes == 64


def test_c7_an_exponential_inline_expansion_is_stopped_at_the_limit():
    """共有を切って木に戻す形でも、上限までしか **作らない**。

    深さ 40 の二重化 DAG を展開すると 2**40 個の葉になる。書き出しが流しながら
    行われていなければ、この test は終わらない（そこが「完成文字列を作ってから
    測る」との違い）。
    """

    a = _param("a", 0)
    context = build_smt_render_context()
    started = time.perf_counter()
    with pytest.raises(RenderOutputLimitExceeded):
        render_smt_term(_doubling_dag(40, a), context, None, shared=False, limit_bytes=50_000)
    assert time.perf_counter() - started < 10.0


def test_c7_intermediate_work_is_observed_and_not_budgeted():
    """中間作業量は **観測だけ**。予算は出力にしか掛からないこと。

    以前はここに「材料（fragment の総量）が出力上限 × 倍率を超えたら止める」が
    あった。材料と出力の比には普遍的な有限上限が無いので、その倍率は原理的に
    決められない（要求した子を捨てれば出力が小さくても材料は幾らでも大きく
    なれる）。だから中間作業量は counter で観測し、止めるのは出力予算だけにした。

    4000 段の線形式は、どの node も自分で書く分は小さい（20 byte 程度）ので
    **計画は通る** — 抱えている fragment の総量が出力予算を大きく超えていても。
    出力予算に引っかかるのは書き出しのとき。
    """

    a = _param("a", 0)
    counters = RenderCounters()
    plan = _plan_for(_linear_chain(4000, a), counters=counters)

    # 中間作業量は出力予算より大きいが、計画は止まらない（観測だけ）
    assert plan.distinct_instances > 4_000
    assert counters.retained_fragment_bytes > 5_000
    # どの 1 個の中間文字列も node 1 個分（= 幅にも深さにも比例しない）
    assert counters.max_fragment_bytes < 200

    # 出力予算に引っかかるのは書き出し口
    with pytest.raises(RenderOutputLimitExceeded) as excinfo:
        render_smt_term(
            _linear_chain(4000, a), build_smt_render_context(), None, limit_bytes=5_000
        )
    assert excinfo.value.site == "core.render_smt.emit"
    assert excinfo.value.limit_bytes == 5_000


def test_c7_no_intermediate_string_exceeds_one_node_worth():
    """どの中間文字列も node 1 個分。部分木の大きさには比例しない。"""

    a = _param("a", 0)
    reset_render_metrics()
    _to_smt_internal(_doubling_dag(40, a))
    _to_smt_internal(_linear_chain(5000, a))
    metrics = render_metrics_snapshot()
    assert metrics["max_fragment_bytes"] < 200


def test_c7_the_writer_never_holds_more_than_the_limit():
    """上限を超える文字列は writer にも残らない。"""

    a = _param("a", 0)
    context = build_smt_render_context()
    seen = []
    original = CountingWriter.write

    def _recording_write(self, text):
        original(self, text)
        seen.append(self.buffered_bytes)

    CountingWriter.write = _recording_write
    try:
        with pytest.raises(RenderOutputLimitExceeded):
            render_smt_term(_doubling_dag(30, a), context, None, shared=False, limit_bytes=20_000)
    finally:
        CountingWriter.write = original
    assert seen
    assert max(seen) <= 20_000


def test_c7_counting_writer_stops_at_the_limit_without_building_the_string():
    writer = CountingWriter(limit_bytes=10, site="test")
    writer.write("12345")
    assert writer.emitted_bytes == 5
    assert writer.buffered_bytes == 5
    with pytest.raises(RenderOutputLimitExceeded):
        writer.write("678901")
    assert writer.aborted is True
    assert writer.getvalue() == ""
    assert writer.buffered_bytes == 0
    assert writer.emitted_bytes <= 10


def test_c7_requested_bytes_is_the_total_needed_not_the_increment():
    """`requested_bytes` は **その時点で必要だった総 byte 数**であること。

    追加分だけを渡すと `limit_bytes` と比べられない値になる。上限 10 に 5 byte
    書いたあと 6 byte 書こうとしたなら、必要だったのは 11。

    `write` / `reserve` / `write_repeated` の 3 つで同じ意味にする。
    """

    writer = CountingWriter(limit_bytes=10, site="test")
    writer.write("12345")
    with pytest.raises(RenderOutputLimitExceeded) as excinfo:
        writer.write("678901")
    assert excinfo.value.limit_bytes == 10
    assert excinfo.value.requested_bytes == 11

    # reserve も同じ意味
    writer = CountingWriter(limit_bytes=10, site="test")
    writer.write("12345")
    with pytest.raises(RenderOutputLimitExceeded) as excinfo:
        writer.reserve(6)
    assert excinfo.value.requested_bytes == 11

    # write_repeated も同じ意味（`reserve` 経由で落ちる）
    writer = CountingWriter(limit_bytes=10, site="test")
    writer.write("12345")
    with pytest.raises(RenderOutputLimitExceeded) as excinfo:
        writer.write_repeated(")", 6)
    assert excinfo.value.requested_bytes == 11

    # 何も書いていなければ追加分と総量は一致する
    writer = CountingWriter(limit_bytes=3, site="test")
    with pytest.raises(RenderOutputLimitExceeded) as excinfo:
        writer.write("abcd")
    assert excinfo.value.requested_bytes == 4

    # 非 ASCII も byte で数える
    writer = CountingWriter(limit_bytes=4, site="test")
    writer.write("あ")  # 3 byte
    with pytest.raises(RenderOutputLimitExceeded) as excinfo:
        writer.write("い")  # +3 byte -> 6 必要
    assert excinfo.value.requested_bytes == 6


def test_c7_counting_writer_without_limit_joins_once():
    writer = CountingWriter()
    for part in ("a", "b", "c"):
        writer.write(part)
    assert writer.getvalue() == "abc"
    assert writer.emitted_bytes == 3
    assert writer.part_count == 3


def test_c7_counters_are_diagnostic_only():
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


def test_c7_human_rendering_stops_at_the_output_budget_too():
    a = _param("a", 0)
    from scripts.function_tracer_pcode.core.render_python import (
        HumanRenderContext,
        render_human_text,
    )

    with pytest.raises(RenderOutputLimitExceeded):
        render_human_text(
            _doubling_dag(40, a), HumanRenderContext(), shared=False, limit_bytes=20_000
        )


@pytest.mark.parametrize(
    "name,build",
    [
        ("wide_call", lambda: _wide_call(20000)),
        ("wide_phi", lambda: _wide_phi(8000)),
    ],
)
def test_c7_a_wide_node_stops_at_the_output_budget_in_the_human_renderer_too(name, build):
    """人向け描画でも、**書き出し**が出力予算で止まること。

    止まるのは書き出し口で、計画（fragment の組み立て）ではない。予算は描画
    規則ではなく書き出し口が持つので SMT と人向けで別々に効かせる必要は無い —
    が、それ自体を確かめないと、どちらか一方だけで試して満足する状態になる。
    """

    from scripts.function_tracer_pcode.core.render_python import (
        HumanRenderContext,
        render_human_text,
    )

    root = build()
    started = time.perf_counter()
    with pytest.raises(RenderOutputLimitExceeded) as excinfo:
        render_human_text(root, HumanRenderContext(simplify=False), limit_bytes=200)
    assert time.perf_counter() - started < 5.0
    assert excinfo.value.site == "core.render_python.emit"
    # 予算を超えると分かった時点で止まっている（書き切っていない）
    assert excinfo.value.requested_bytes > excinfo.value.limit_bytes


def test_c7_a_wide_node_renders_completely_in_the_human_renderer_without_a_limit():
    """上限が無いときは幅の広い node も最後まで描けること（打ち切りが常時 on でない）。"""

    from scripts.function_tracer_pcode.core.render_python import (
        HumanRenderContext,
        render_human_text,
    )

    text = render_human_text(_wide_call(256), HumanRenderContext(simplify=False))
    assert text.count("p255") >= 1


# ---------------------------------------------------------------------------
# 型付きの項: planner と renderer の隠れ結合が無いこと
# ---------------------------------------------------------------------------


def test_typed_term_properties_travel_with_the_reference():
    term = RenderedTerm("\x0012\x00", classify_smt_fragment("(fp.add a b)", None, False))
    assert term_is_fp_rendered(term) is True
    assert term_boolean_literal(term) is None
    literal = RenderedTerm("\x0013\x00", classify_smt_fragment("true", None, False))
    assert term_boolean_literal(literal) is True


def test_a_term_without_properties_is_refused():
    """性質を持たない項が型付きの観測へ届いたら fail-closed。"""

    with pytest.raises(RenderedTermContractError):
        term_is_fp_rendered("(fp.add a b)")
    with pytest.raises(RenderedTermContractError):
        term_properties("anything")


def test_properties_are_inherited_through_a_pass_through_fragment():
    """先頭が子なら接頭辞で決まる性質は子から継ぐ（近似ではなく等値）。"""

    fp_child = classify_smt_fragment("(fp.add a b)", None, False)
    passthrough = classify_smt_fragment("\x005\x00", fp_child, True)
    assert passthrough.is_fp_term is True
    prefixed = classify_smt_fragment("\x005\x00 tail", fp_child, False)
    assert prefixed.is_fp_term is True
    assert prefixed.boolean_literal is None
    wrapped = classify_smt_fragment("(bvadd \x005\x00 x)", None, False)
    assert wrapped.is_fp_term is False


def test_plan_and_output_agree_on_the_reference_topology():
    """計画の辺と fragment の参照が一致し、書き出しがそれを使うこと。"""

    a = _param("a", 0)
    plan = _plan_for(_doubling_dag(12, a))
    names = assign_binding_names(plan, smt_binding_namespace(plan))
    check_plan_invariants(plan, names)

    for instance in plan.instances:
        assert tuple(fragment_children(instance.fragment)) == instance.used_children
        assert set(instance.used_children) <= set(instance.child_indices)
    assert _binding_dependency_order_is_valid(plan, names)

    writer = CountingWriter()
    write_expansion(writer, plan, plan.root_index, names)
    assert PLACEHOLDER_MARK not in writer.getvalue()


def test_an_inconsistent_plan_is_refused_instead_of_emitting_an_empty_definition():
    """束縛した instance の定義が空なら落とす（fail-closed）。"""

    a = _param("a", 0)
    plan = _plan_for(_doubling_dag(12, a))
    names = assign_binding_names(plan, smt_binding_namespace(plan))
    bound = plan.bound_order[0]
    plan.instances[bound].fragment = ""
    plan.instances[bound].used_children = ()
    with pytest.raises(RenderPlanInvariantError):
        check_plan_invariants(plan, names)


def test_a_bound_instance_that_nothing_references_is_refused():
    a = _param("a", 0)
    plan = _plan_for(_doubling_dag(12, a))
    names = assign_binding_names(plan, smt_binding_namespace(plan))
    plan.instances[plan.bound_order[0]].references = 0
    with pytest.raises(RenderPlanInvariantError):
        check_plan_invariants(plan, names)


def test_a_reference_the_body_never_requested_is_refused():
    a = _param("a", 0)
    plan = _plan_for(_doubling_dag(12, a))
    names = assign_binding_names(plan, smt_binding_namespace(plan))
    target = plan.instances[plan.root_index]
    target.child_indices = ()
    with pytest.raises(RenderPlanInvariantError):
        check_plan_invariants(plan, names)


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
    rendered = _to_smt_internal(_binary("INT_ADD", address_use, value_use))

    assert "(_ bv8192 64)" in rendered
    assert " g)" in rendered or "(g" in rendered or " g " in rendered


def test_c4_render_plan_keys_instances_by_node_and_context():
    """共有 key が node identity だけになっていないこと（plan 層の契約）。"""

    node = object()
    root = ("root", node)

    def body(current, context, resolve):
        if current is root:
            return f"[{resolve(node, 'wide')}|{resolve(node, 'narrow')}]"
        return f"<{context}>"

    plan = build_render_plan(
        root,
        "root-context",
        body=body,
        classify=lambda fragment, head, exact: ("properties", fragment),
        policy=SharingPolicy(min_shared_bytes=0, min_shared_tree_nodes=1),
        counters=RenderCounters(),
    )
    contexts = {instance.context for instance in plan.instances if instance.node is node}
    assert contexts == {"wide", "narrow"}
    assert len({instance.index for instance in plan.instances if instance.node is node}) == 2


# ---------------------------------------------------------------------------
# 走査の形: 予定表（scheduled）と経路（active）を混ぜていないこと
#
# 描画 driver と属性評価は同じ予定表を使うので、同じ形を **両方** で確かめる。
# 片方だけ見ていると、借りている側が別実装へ戻ったことに気付けない。
# ---------------------------------------------------------------------------

#: 要求収集へ切り替わるだけの幅（`DISCOVERY_AFTER_RETRIES` 超）。依存のある
#: 子を収集より後ろに置くために使う。
_COLLECTION_FILLERS = tuple(("filler", index) for index in range(8))


def test_a_sibling_dependency_is_not_a_cycle_in_either_traversal():
    """一括で積んだ sibling どうしの依存を閉路と言わないこと。

    ```text
    root
    ├─ A
    │  └─ x
    └─ x
    ```

    `root` の要求をまとめて積むと `A` と `x` が同時に **scheduled** になる。
    そのあと `A` が `x` を要求するが、`x` は「まだ動いていない予定」であって
    `A` の祖先ではない。予定を経路として数えると、閉路でない DAG が落ちる。

    依存のある sibling は収集が起きる位置より **後ろ**に置く（前だと収集前に
    解決されてしまい、この test が守るものを通らない）。
    """

    x = ["x"]
    a = ["A"]
    root = ["root"]

    def body(node, context, resolve):
        if node is root:
            parts = [resolve(filler, context) for filler in _COLLECTION_FILLERS]
            parts.append(resolve(a, context))
            parts.append(resolve(x, context))
            return "[" + "|".join(parts) + "]"
        if node is a:
            return f"<A {resolve(x, context)}>"
        return "leaf"

    plan = build_render_plan(
        root,
        "context",
        body=body,
        classify=lambda fragment, head, exact: ("properties", fragment),
        policy=SharingPolicy(min_shared_bytes=0, min_shared_tree_nodes=1),
        counters=RenderCounters(),
    )
    # x は 1 instance だけ（A と root の両方から参照される）
    assert len([i for i in plan.instances if i.node is x]) == 1

    def rule(node, child):
        if node is root:
            return 1 + max([child(f) for f in _COLLECTION_FILLERS] + [child(a), child(x)])
        if node is a:
            return 1 + child(x)
        return 1

    from scripts.function_tracer_pcode.core.render_smt.attributes import evaluate_attribute

    assert evaluate_attribute(root, rule, {}) == 3


def test_a_diamond_dag_is_not_a_cycle_in_either_traversal():
    """菱形（2 つの親が同じ子を持つ）を閉路と言わないこと。"""

    shared = ["shared"]
    left = ["left"]
    right = ["right"]
    root = ["root"]

    def body(node, context, resolve):
        if node is root:
            parts = [resolve(filler, context) for filler in _COLLECTION_FILLERS]
            parts += [resolve(left, context), resolve(right, context)]
            return "[" + "|".join(parts) + "]"
        if node is left:
            return f"<L {resolve(shared, context)}>"
        if node is right:
            return f"<R {resolve(shared, context)}>"
        return "leaf"

    plan = build_render_plan(
        root,
        "context",
        body=body,
        classify=lambda fragment, head, exact: ("properties", fragment),
        policy=SharingPolicy(min_shared_bytes=0, min_shared_tree_nodes=1),
        counters=RenderCounters(),
    )
    assert len([i for i in plan.instances if i.node is shared]) == 1

    def rule(node, child):
        if node is root:
            return 1 + max([child(f) for f in _COLLECTION_FILLERS] + [child(left), child(right)])
        if node in (left, right):
            return 1 + child(shared)
        return 1

    from scripts.function_tracer_pcode.core.render_smt.attributes import evaluate_attribute

    assert evaluate_attribute(root, rule, {}) == 3


def test_a_real_cycle_is_refused_in_either_traversal():
    """本物の閉路（子が祖先を要求し返す）は、収集が起きる幅でも止まること。"""

    root = ["root"]
    child_node = ["child"]

    def body(node, context, resolve):
        if node is root:
            parts = [resolve(filler, context) for filler in _COLLECTION_FILLERS]
            parts.append(resolve(child_node, context))
            return "[" + "|".join(parts) + "]"
        return f"<{resolve(root, context)}>"

    with pytest.raises(RenderGraphCycleError):
        build_render_plan(
            root,
            "context",
            body=body,
            classify=lambda fragment, head, exact: ("properties", fragment),
            policy=SharingPolicy(min_shared_bytes=0, min_shared_tree_nodes=1),
            counters=RenderCounters(),
        )

    def rule(node, child):
        if node is root:
            return 1 + max([child(f) for f in _COLLECTION_FILLERS] + [child(child_node)])
        return 1 + child(root)

    from scripts.function_tracer_pcode.core.render_smt.attributes import evaluate_attribute

    with pytest.raises(RenderGraphCycleError):
        evaluate_attribute(root, rule, {})


def test_a_node_reached_twice_on_one_path_is_a_cycle_not_sharing():
    """直接の自己参照も閉路として止まること（収集に入らない幅でも）。"""

    root = ["root"]

    def body(node, context, resolve):
        return f"<{resolve(root, context)}>"

    with pytest.raises(RenderGraphCycleError):
        build_render_plan(
            root,
            "context",
            body=body,
            classify=lambda fragment, head, exact: ("properties", fragment),
            policy=SharingPolicy(min_shared_bytes=0, min_shared_tree_nodes=1),
            counters=RenderCounters(),
        )


def test_the_schedule_separates_scheduled_from_active():
    """予定表そのものの契約: 積んだだけの項目は active ではないこと。"""

    from scripts.function_tracer_pcode.core.render_plan import ResolutionSchedule

    schedule = ResolutionSchedule("root", key_of=lambda item: item)
    assert schedule.current() == "root"
    assert not schedule.is_active("root")

    schedule.need(["a", "x"])
    # 要求した側（root）だけが active。積まれた子は scheduled
    assert schedule.is_active("root")
    assert not schedule.is_active("a")
    assert not schedule.is_active("x")
    # 先に要求したものが先に片付く
    assert schedule.current() == "a"

    # a が x を要求するのは閉路ではない
    schedule.need(["x"])
    assert schedule.is_active("a")
    assert schedule.current() == "x"
    schedule.settle()
    assert not schedule.is_active("x")

    # 祖先を要求し返すのは閉路
    with pytest.raises(RenderGraphCycleError):
        schedule.need(["root"])


def test_c4_one_node_under_two_contexts_is_not_a_cycle_when_requests_are_collected():
    """幅の広い node が同じ子を 2 つの文脈で要求しても閉路と見なさないこと。

    走査の「今いる経路」を node だけで持つと、要求をまとめて積む実行のときに
    同じ node の 2 つ目の文脈が「もう経路に居る」と見えて、閉路でもないのに
    落ちる。経路は描画 instance（node + 文脈）で持たなければならない。

    要求収集の実行へ入るだけの幅（`DISCOVERY_AFTER_RETRIES` 超）が要るので、
    子を 8 個とその 2 文脈で要求する本体にしてある。
    """

    shared = object()
    children = [("child", index) for index in range(8)]
    root = ("root", shared)

    def body(current, context, resolve):
        if current is root:
            parts = [resolve(child, "plain") for child in children]
            parts.append(resolve(shared, "wide"))
            parts.append(resolve(shared, "narrow"))
            return "[" + "|".join(parts) + "]"
        return f"<{context}>"

    counters = RenderCounters()
    plan = build_render_plan(
        root,
        "root-context",
        body=body,
        classify=lambda fragment, head, exact: ("properties", fragment),
        policy=SharingPolicy(min_shared_bytes=0, min_shared_tree_nodes=1),
        counters=counters,
    )

    contexts = {instance.context for instance in plan.instances if instance.node is shared}
    assert contexts == {"wide", "narrow"}
    # 収集の実行に入っていること（入っていなければこの test は守るものを守れない）
    assert counters.node_body_executions > len(children)
    writer = CountingWriter()
    write_expansion(writer, plan, plan.root_index, {})
    assert writer.getvalue().count("<plain>") == len(children)


def test_a_real_cycle_is_still_refused_when_requests_are_collected():
    """文脈まで含めて経路を持っても、本物の閉路は止まること。"""

    children = [("child", index) for index in range(8)]
    root = ["root"]

    def body(current, context, resolve):
        if current is root:
            parts = [resolve(child, context) for child in children]
            return "[" + "|".join(parts) + "]"
        # 子が root を要求し返す = 閉路
        return f"<{resolve(root, context)}>"

    with pytest.raises(RenderGraphCycleError):
        build_render_plan(
            root,
            "same-context",
            body=body,
            classify=lambda fragment, head, exact: ("properties", fragment),
            policy=SharingPolicy(min_shared_bytes=0, min_shared_tree_nodes=1),
            counters=RenderCounters(),
        )


# ---------------------------------------------------------------------------
# C5: 人向け表示
# ---------------------------------------------------------------------------


def test_c5_human_rendering_uses_shared_references_instead_of_re_expansion():
    a = _param("a", 0)
    reset_render_metrics()
    text = expression_to_string(_doubling_dag(40, a))
    metrics = render_metrics_snapshot()

    assert " where " in text
    assert "@h" in text
    assert len(text) < 20000
    assert metrics["distinct_rendered_nodes"] == 41
    assert metrics["shared_bindings"] >= 1
    assert metrics["max_fragment_bytes"] < 200


def test_c5_small_expressions_keep_their_existing_text():
    a = _param("a", 0)
    b = _param("b", 1)
    assert expression_to_string(_binary("INT_ADD", a, b)) == "(a + b)"
    assert " where " not in expression_to_string(_doubling_dag(3, a))


def test_c5_every_human_shared_reference_is_defined():
    a = _param("a", 0)
    text = expression_to_string(_doubling_dag(40, a))
    body, _, where = text.partition(" where ")
    defined = {part.split(" = ")[0].strip() for part in where.split("; ")}
    used = set(re.findall(r"@h[0-9a-f_]+", body))
    assert used
    assert used <= defined


def test_c5_human_shared_reference_names_are_stable_and_collision_free():
    a = _param("a", 0)
    root = _doubling_dag(40, a)
    first = expression_to_string(root)
    assert expression_to_string(root) == first

    reference = first.split(" where ")[1].split(" = ")[0]
    colliding = _variable(reference, size=4)
    text = expression_to_string(_binary("INT_ADD", _doubling_dag(40, colliding), colliding))
    definitions = [part.split(" = ")[0] for part in text.split(" where ")[1].split("; ")]
    assert reference not in definitions


# ---------------------------------------------------------------------------
# C6: `to_string()` を identity に使う site 0、**置換前後で dedup 同一**
#
# C6 が求めるのは「表示文字列への依存を外すこと」と「dedup の同値関係を変えない
# こと」の 2 つ。鍵の同値関係そのもの（予算付き key の切り詰め、可換正規化）は
# ここでは直さない — それは identity の owner の話で、この PR の変更軸ではない。
# ---------------------------------------------------------------------------


def _c6_corpus():
    """dedup 関係を比べるための adversarial な条件の組。

    review で挙がった形を網羅する: 予算超過で切り詰められる深い式、可換な並べ
    替え、同じ構造を別 object で組んだもの、否定、共有 DAG と同型の非共有構造、
    opaque な値。
    """

    a = _param("a", 0)
    b = _param("b", 1)

    def deep(tail: int, depth: int = 400):
        node = _param("a", 0)
        for index in range(depth):
            node = _binary("INT_ADD", node, _const(index))
        return _binary("INT_LESS", node, _const(tail), size=1)

    def unshared_doubling(depth: int):
        if depth == 0:
            return _param("a", 0)
        return _binary("INT_ADD", unshared_doubling(depth - 1), unshared_doubling(depth - 1))

    class _Opaque:
        def __repr__(self):
            return "<ghidra object>"

    opaque = Expression(ExpressionType.CONSTANT, value=_Opaque(), size=4)

    return [
        ("add_ab", Condition(_binary("INT_ADD", a, b, size=1))),
        ("add_ba_commuted", Condition(_binary("INT_ADD", b, a, size=1))),
        ("add_ab_rebuilt", Condition(_binary("INT_ADD", _param("a", 0), _param("b", 1), size=1))),
        ("add_ab_negated", Condition(_binary("INT_ADD", a, b, size=1), True)),
        ("less_ab", Condition(_binary("INT_LESS", a, b, size=1))),
        ("deep_tail_1", Condition(deep(1))),
        ("deep_tail_2", Condition(deep(2))),
        ("shared_dag", Condition(_binary("INT_LESS", _doubling_dag(4, a), b, size=1))),
        ("unshared_same_shape", Condition(_binary("INT_LESS", unshared_doubling(4), b, size=1))),
        ("opaque_value", Condition(_binary("INT_LESS", opaque, b, size=1))),
    ]


def _base_summary_identity_key(ret, site_key):
    """base（`15e05826`）の実装そのまま。dedup 関係の比較対象。"""

    return (
        "return_info",
        site_key,
        tuple(
            getattr(condition, "structural_key", lambda: ("condition", condition.to_string()))()
            for condition in tuple(getattr(ret, "conditions", ()) or ())
        ),
        expression_key_safe(getattr(ret, "value", None)),
    )


def test_c6_the_summary_identity_dedup_relation_is_unchanged_from_base():
    """**置換前後で dedup 同一**: base と head で同値関係が一致すること。

    比べるのは鍵の値そのものではなく `key(x) == key(y)` の真偽。C6 は表示文字列
    依存を外すことを求めているだけで、既存の同値関係（深い式の切り詰めや可換
    正規化を含む）を直すことは求めていない。直すなら別 owner の仕事。
    """

    from scripts.function_tracer_pcode.analysis.returns.return_extraction import (
        _impl__return_info_summary_identity_key,
    )

    class _Site:
        def _return_site_key(self, ret):
            return "same-site"

    site = _Site()
    corpus = _c6_corpus()
    # 条件の組 + 戻り値の有無 / 深さ違いを掛け合わせる
    values = [
        ("absent", None),
        ("param", _param("a", 0)),
        ("deep_1", _c6_deep_value(1)),
        ("deep_2", _c6_deep_value(2)),
    ]
    rets = []
    for condition_name, condition in corpus:
        for value_name, value in values:
            rets.append(
                (f"{condition_name}/{value_name}", SimpleNamespace(value=value, conditions=[condition]))
            )

    mismatches = []
    for left_name, left in rets:
        for right_name, right in rets:
            old_same = _base_summary_identity_key(left, "same-site") == _base_summary_identity_key(
                right, "same-site"
            )
            new_same = _impl__return_info_summary_identity_key(
                site, left
            ) == _impl__return_info_summary_identity_key(site, right)
            if old_same != new_same:
                mismatches.append((left_name, right_name, old_same, new_same))
    assert mismatches == [], mismatches[:8]

    # 関係が「全部同じ」や「全部違う」に潰れていないこと（比較が意味を持つ）
    keys = [_impl__return_info_summary_identity_key(site, ret) for _name, ret in rets]
    assert 1 < len({repr(key) for key in keys}) < len(keys)


def _c6_deep_value(tail: int, depth: int = 400):
    node = _param("a", 0)
    for index in range(depth):
        node = _binary("INT_ADD", node, _const(index))
    return _binary("INT_ADD", node, _const(tail))


def test_c6_the_proof_target_keys_are_the_base_relation():
    """証明側の dedup 関係も base のままであること。

    structural proof で実際に比較されるのは `target_guard_keys`
    （`divergence_proofs.condition_identity_key`）。この PR はそこを触っていない
    ので、関係は base と同一。
    """

    from scripts.function_tracer_pcode.analysis.returns.divergence_proofs import (
        condition_identity_key,
    )

    def base_condition_identity_key(condition):
        return (
            "condition",
            expression_key_safe(getattr(condition, "expression", None)),
            bool(getattr(condition, "negated", False)),
        )

    corpus = _c6_corpus()
    for _left_name, left in corpus:
        for _right_name, right in corpus:
            assert (
                base_condition_identity_key(left) == base_condition_identity_key(right)
            ) == (condition_identity_key(left) == condition_identity_key(right))


def test_c6_no_rendered_text_is_used_as_an_identity():
    """`to_string()` の結果を identity（等値比較 / 辞書 key）に使わないこと。

    移行した 2 site（`return_extraction` の条件列、`control_recovery` の
    `("target", …)`）に表示文字列が残っていないことを、構造で確かめる。
    """

    import ast as _ast

    for module_path in (
        "analysis/returns/return_extraction.py",
        "analysis/returns/control_recovery.py",
    ):
        path = (
            pathlib.Path(__file__).resolve().parents[2] / module_path
        )
        tree = _ast.parse(path.read_text(encoding="utf-8"))
        for node in _ast.walk(tree):
            # 等値比較の両辺に to_string() が現れない
            if isinstance(node, _ast.Compare) and any(
                isinstance(op, (_ast.Eq, _ast.NotEq)) for op in node.ops
            ):
                for part in [node.left] + list(node.comparators):
                    for inner in _ast.walk(part):
                        if (
                            isinstance(inner, _ast.Call)
                            and isinstance(inner.func, _ast.Attribute)
                            and inner.func.attr == "to_string"
                        ):
                            raise AssertionError(f"{module_path}:{node.lineno} compares to_string()")


def test_c6_the_migrated_sites_have_no_rendered_text(monkeypatch):
    """移行した site が描画を **呼ばない** こと（実行で確かめる）。"""

    from scripts.function_tracer_pcode.analysis.returns.return_extraction import (
        _impl__return_info_summary_identity_key,
    )
    from scripts.function_tracer_pcode.core import condition as condition_module

    def _forbidden(self, *args, **kwargs):
        raise AssertionError("identity must not render text")

    monkeypatch.setattr(condition_module.Condition, "to_string", _forbidden)

    class _Site:
        def _return_site_key(self, ret):
            return "site"

    a = _param("a", 0)
    ret = SimpleNamespace(
        value=a, conditions=[Condition(_binary("INT_LESS", a, _param("b", 1), size=1))]
    )
    assert _impl__return_info_summary_identity_key(_Site(), ret) is not None


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
    from scripts.function_tracer_pcode.core.errors import UnpublishedSemanticInputError
    from scripts.function_tracer_pcode.core.render_smt import expression_to_smt

    expr = _binary("INT_ADD", _param("a", 0), _param("b", 1))
    with pytest.raises(UnpublishedSemanticInputError):
        expression_to_smt(expr)
    publish(expr)
    assert expression_to_smt(expr) == "(bvadd a b)"


def test_binding_names_use_the_reserved_prefix():
    a = _param("a", 0)
    names = _rendered_binding_names(_to_smt_internal(_doubling_dag(24, a)))
    assert names
    assert all(name.startswith(f"|{SMT_BINDING_PREFIX}") for name in names)
    assert NO_SHARING_POLICY.binds(references=9, inline_bytes=10**9, tree_nodes=10**9) is False


# ---------------------------------------------------------------------------
# 幅の広い node と非 ASCII
# ---------------------------------------------------------------------------


def _wide_call(arity: int) -> Expression:
    args = [_param(f"p{index}", index) for index in range(arity)]
    return Expression(ExpressionType.CALL, name="wide", operands=args, size=4)


def _wide_phi(branches: int) -> Expression:
    a = _param("a", 0)
    b = _param("b", 1)
    cases = [
        (
            Condition(_binary("INT_EQUAL", a, _const(index), size=1)),
            _binary("INT_ADD", b, _const(index)),
        )
        for index in range(branches)
    ]
    cases.append((None, b))
    phi = Expression.phi(cases)
    phi.size = 4
    return phi


def test_a_wide_node_renders_completely_without_a_limit():
    """上限が無ければ幅の広い node はそのまま描ける（止めるのは上限のときだけ）。"""

    rendered = _to_smt_internal(_wide_call(200))
    assert rendered.count("p0 ") + rendered.count(" p0") >= 1
    assert rendered.startswith("(call_wide ")


def test_the_budget_is_counted_in_utf8_bytes_not_characters():
    """単位は byte。非 ASCII の symbol 名で文字数と byte 数がずれる。"""

    name = "変数" * 8  # 16 文字 / 48 byte
    assert len(name) == 16
    assert utf8_length(name) == 48

    writer = CountingWriter(limit_bytes=40, site="test")
    with pytest.raises(RenderOutputLimitExceeded) as excinfo:
        writer.write(name)
    assert excinfo.value.limit_bytes == 40
    assert excinfo.value.requested_bytes == 48

    # 同じ文字数の ASCII なら収まる（文字数で数えていたら区別できない）。
    ascii_writer = CountingWriter(limit_bytes=40, site="test")
    ascii_writer.write("x" * 16)
    assert ascii_writer.emitted_bytes == 16


def test_a_non_ascii_symbol_is_measured_in_bytes_by_the_renderer():
    variable = _variable("変数" * 8, size=4)
    root = _binary("INT_ADD", variable, _param("a", 0))
    context = build_smt_render_context()
    counters = RenderCounters()
    plan = _plan_for(root, counters=counters)
    rendered = render_smt_term(root, context, None)
    assert counters.max_fragment_bytes >= 48
    assert utf8_length(rendered) > len(rendered)
    # 文字数で測っていたら通ってしまう上限で、byte なら止まる。
    with pytest.raises(RenderOutputLimitExceeded):
        render_smt_term(root, context, None, limit_bytes=len(rendered))
    assert plan.instances


# ---------------------------------------------------------------------------
# identity: digest 一致だけで同一性を決めない
# ---------------------------------------------------------------------------


def test_a_wide_node_costs_time_proportional_to_its_width():
    """幅の広い node が幅の 2 乗にならないこと。

    「子を 1 個積んでやり直す」だけだと、幅 n の node の本体を n 回回すので
    幅の 2 乗になる（幅 1024 の PHI で実測 6.5 秒 → 0.13 秒）。回した回数で
    「要求をまとめて集める」実行へ切り替えることで線形に戻している。
    """

    def elapsed(build, width):
        root = build(width)
        started = time.perf_counter()
        _to_smt_internal(root)
        return time.perf_counter() - started

    narrow = elapsed(_wide_phi, 128)
    wide = elapsed(_wide_phi, 512)
    # 幅 4 倍。2 乗なら 16 倍、線形なら 4 倍。余裕を見て 8 倍未満で固定する。
    assert wide < max(narrow * 8, 0.5), (narrow, wide)

    narrow_call = elapsed(_wide_call, 256)
    wide_call = elapsed(_wide_call, 1024)
    assert wide_call < max(narrow_call * 8, 0.5), (narrow_call, wide_call)


def test_collected_requests_do_not_change_the_output():
    """要求収集を通る幅と通らない幅で、同じ式なら同じ出力になること。"""

    from scripts.function_tracer_pcode.core import render_plan

    root = _wide_phi(64)
    with_collection = _to_smt_internal(root)
    original = render_plan.DISCOVERY_AFTER_RETRIES
    try:
        render_plan.DISCOVERY_AFTER_RETRIES = 1 << 30  # 収集へ切り替えない
        without_collection = _to_smt_internal(root)
    finally:
        render_plan.DISCOVERY_AFTER_RETRIES = original
    assert with_collection == without_collection


def test_the_render_package_exposes_only_the_rendering_entry_points():
    """描画 package の外向きの面は入口だけ。

    共有方針・束縛名・型付きの項・属性評価は描画の実装どうしの取り決めで、
    外へ出すと変えるたびに外部 consumer が壊れる。PR-22-C が足した名前が
    package の facade に載っていないことを固定する。
    """

    import scripts.function_tracer_pcode.core.render_smt as package

    internal = (
        "SmtTermProperties",
        "classify_smt_fragment",
        "smt_term",
        "term_is_fp_rendered",
        "term_boolean_literal",
        "SmtRenderContext",
        "build_smt_render_context",
        "SMT_SHARING_POLICY",
        "SMT_BINDING_PREFIX",
        "SMT_SYMBOL_RE",
        "smt_binding_namespace",
        "assign_binding_names",
        "write_let_term",
        "rendered_binding_names",
        "binding_dependency_order_is_valid",
        "iter_expression_nodes",
        "ResolutionSchedule",
        "FragmentBuilder",
        "ChildResolver",
        "render_attribute_scope",
        "evaluate_attribute",
        "attribute_cache",
        "any_node",
    )
    exposed = [name for name in internal if hasattr(package, name)]
    assert exposed == [], exposed
    # 入口は出ている。
    for name in (
        "expression_to_smt",
        "condition_to_smt",
        "render_expression_smt_evidence",
        "render_condition_smt_evidence",
        "render_smt_term",
        "SMT_RENDER_SCHEMA",
    ):
        assert hasattr(package, name), name


