# -*- coding: utf-8 -*-
"""Issue #105 PR-105-A: 条件の identity と cache（計画 v5 §4.2 / §6.B-1、D1〜D4・D8・D9・D11〜D13）。

固定する契約:

* hash / digest だけで一致を確定しない（bucket → 完全比較）。digest を定数にしても
  誤った hit は 0（性能の問題に留まる）
* 条件 oracle は **script を組む前** に identity で cache を引き、記憶した `None` も hit
* symbol の割当（`objvar_<n>`）は identity の canonical な順（入力順・出会い順に依らない）
* 書き換えの identity は root graph + mapping の全体 + 描画文脈 + schema（root だけで
  memo しない）
* cache の寿命は pair（pair 境界の scope）。scope の外では何も覚えない
* 計測は cache・判定と独立で、結果 JSON の診断に出る
"""

from __future__ import annotations

import ast
import dataclasses
import pathlib
import time
from types import SimpleNamespace
from unittest.mock import patch

import pytest
import z3

from scripts.function_tracer_pcode.analysis.condition import condition_cache, query_identity
from scripts.function_tracer_pcode.analysis.condition.condition_cache import (
    active_condition_cache,
    cache_lookup,
    cache_store,
    condition_cache_scope,
    root_memo,
)
from scripts.function_tracer_pcode.core.condition_metrics import (
    active_condition_metrics,
    condition_metrics_scope,
)
from scripts.function_tracer_pcode.analysis.condition.query_identity import (
    ORACLE_RENDER_CONTEXT,
    RenderContext,
    RewriteIdentity,
    RootQueryGraph,
    SolverQueryIdentity,
    root_query_graph,
)
from scripts.function_tracer_pcode.analysis.condition.simplifier import (
    ConditionSimplifier,
    ConditionSMTOracle,
)
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
)
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.storage import StorageInfo
from scripts.function_tracer_pcode.core.structural import (
    ConditionsSignature,
    condition_key,
    key_contains_placeholder,
)


PACKAGE_ROOT = pathlib.Path(__file__).resolve().parents[2]


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------


def _const(value, size=4):
    return Expression.constant(value, size=size)


def _param(name, index, size=4, ref_index=None):
    return Expression.parameter(
        name,
        index=index,
        size=size,
        runtime_ref=LocationBaseRef.parameter(
            name, index=index if ref_index is None else ref_index
        ),
    )


def _storage_param(offset, size=4):
    return Expression.parameter(
        "param_s",
        index=-1,
        size=size,
        storage_info=StorageInfo(
            is_register=False, space_id=0, offset=offset, size=size, size_bits=size * 8
        ),
    )


def _eq(left, right):
    return Condition(Expression.binary_op("INT_EQUAL", left, right))


def _slt(left, right):
    return Condition(Expression.binary_op("INT_SLESS", left, right))


def _query(*conditions, context=ORACLE_RENDER_CONTEXT):
    return SolverQueryIdentity.from_conditions(conditions, render_context=context)


class _ConstantDigest:
    """blake2b の代わり: 何を入れても同じ digest（衝突を強制する）。"""

    def __init__(self, data=b"", *, digest_size=16, person=b""):
        self.digest_size = digest_size

    def update(self, _data):
        return None

    def digest(self):
        return b"\x00" * self.digest_size

    def hexdigest(self):
        return self.digest().hex()


@pytest.fixture
def forced_collisions(monkeypatch):
    """外側の fast・graph digest・mapping digest・node の candidate hash をすべて衝突させる。"""

    monkeypatch.setattr(query_identity, "hashlib", SimpleNamespace(blake2b=_ConstantDigest))
    monkeypatch.setattr(query_identity, "encode_stable_atoms", lambda _value: b"")
    monkeypatch.setattr(structural, "candidate_hash", lambda _expr: b"\x07" * 16)


@pytest.fixture
def scoped():
    with condition_cache_scope() as store, condition_metrics_scope() as metrics:
        yield SimpleNamespace(store=store, metrics=metrics)


class _FakeZ3:
    """z3 の代わり（Solver の生成と check の回数を数える）。"""

    sat = object()
    unsat = object()

    def __init__(self, answer="unknown", reason="timeout", raises=None):
        self.answer = answer
        self.reason = reason
        self.raises = raises
        self.solvers = 0
        self.checks = 0

    def Context(self):
        # Issue #161: oracle は query ごとに専用の context（`isolated_solver`）を作る
        return object()

    def Solver(self, ctx=None):
        fake = self
        self.solvers += 1

        class _Solver:
            def set(self, *_args):
                return None

            def add(self, *_args):
                return None

            def check(self):
                fake.checks += 1
                if fake.raises is not None:
                    raise fake.raises
                return {"sat": fake.sat, "unsat": fake.unsat}.get(fake.answer, object())

            def reason_unknown(self):
                return fake.reason

        return _Solver()

    def parse_smt2_string(self, _script, ctx=None):
        return []


def _count_builds(monkeypatch):
    calls = []
    original = ConditionSMTOracle._build_script.__func__

    def _counting(cls, conditions, **kwargs):
        calls.append(len(conditions))
        return original(cls, conditions, **kwargs)

    monkeypatch.setattr(ConditionSMTOracle, "_build_script", classmethod(_counting))
    return calls


# ---------------------------------------------------------------------------
# D1: 条件簡約の経路に `repr` 順の key が無い
# ---------------------------------------------------------------------------


def _repr_sort_sites(tree):
    sites = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        for keyword in node.keywords:
            if keyword.arg != "key":
                continue
            value = keyword.value
            if isinstance(value, ast.Name) and value.id == "repr":
                sites.append(node.lineno)
            elif isinstance(value, ast.Lambda) and any(
                isinstance(inner, ast.Call)
                and isinstance(inner.func, ast.Name)
                and inner.func.id == "repr"
                for inner in ast.walk(value.body)
            ):
                sites.append(node.lineno)
    return sites


def test_d1_condition_simplification_has_no_repr_ordered_keys():
    """D1-A（本 PR）: `analysis/condition/` の key・並べ替えに `repr` を使わない。

    計画 D1 は 2 つの責務に分かれる。D1-A（`repr` 依存の条件 / query identity・並べ替えの
    撤去）は本 PR、D1-B（`not cls._clauses_satisfiability(...)` の禁止）は `SatVerdict`
    を入れた PR-105-B（`test_d1b_the_boolean_negation_of_dpll_is_gone`）。

    `analysis/returns/lifecycle.py` の scope key（storage の束縛の並べ替え）は対象外:
    その key は `AnalysisSnapshot` の意味 fingerprint（`analysis_scope_key`）に入るので、
    並べ方を変えると digest が動く（計画 §6.B-1 の「digest に入らない場合に限り」の条件を
    満たさない。storage identity の tuple の `repr` は決定的なので正しさの問題は無い）。
    """

    offenders = {}
    for path in sorted((PACKAGE_ROOT / "analysis" / "condition").glob("*.py")):
        sites = _repr_sort_sites(ast.parse(path.read_text(encoding="utf-8")))
        if sites:
            offenders[path.name] = sites
    assert offenders == {}


def test_d1b_the_boolean_negation_of_dpll_is_gone():
    """D1-B: DPLL の答えの二値の否定（`not cls._clauses_satisfiability(...)`）は 0 箇所。

    PR-105-A で `_clause_set_is_unsat` 1 箇所へ集約し、PR-105-B が三値の `SatVerdict`
    （`as_unsat_answer()`）へ置き換えた。旧名 `_clauses_are_satisfiable` も含めて数える。
    三値の真偽値化そのものの禁止（`if verdict:` など）は
    `test_issue105b_simplify_budgets.py` の D1-B / D5 の test が固定する。
    """

    tree = ast.parse((PACKAGE_ROOT / "analysis" / "condition" / "simplifier_cnf.py").read_text(encoding="utf-8"))
    owners = []
    for function in ast.walk(tree):
        if not isinstance(function, ast.FunctionDef):
            continue
        for node in ast.walk(function):
            if (
                isinstance(node, ast.UnaryOp)
                and isinstance(node.op, ast.Not)
                and isinstance(node.operand, ast.Call)
                and isinstance(node.operand.func, ast.Attribute)
                and node.operand.func.attr in {"_clauses_are_satisfiable", "_clauses_satisfiability"}
            ):
                owners.append(function.name)
    assert owners == []


def test_d1_the_ast_rule_detects_both_repr_forms():
    tree = ast.parse("x.sort(key=repr)\nsorted(y, key=lambda item: repr(item[0]))\n")
    assert _repr_sort_sites(tree) == [1, 2]


# ---------------------------------------------------------------------------
# D2 / D8: 条件の structural identity（bucket → 完全比較）
# ---------------------------------------------------------------------------


def _deep_chain(leaf, depth):
    expr = leaf
    for _ in range(depth):
        expr = Expression.binary_op("INT_ADD", expr, _const(1))
    return Expression.binary_op("INT_EQUAL", expr, _const(7))


def test_d2_signature_is_an_order_independent_multiset():
    a = _eq(_param("param_1", 0), _const(1))
    b = _slt(_param("param_2", 1), _const(5))
    a_copy = _eq(_param("param_1", 0), _const(1))

    assert ConditionsSignature([a, b]) == ConditionsSignature([b, a_copy])
    assert hash(ConditionsSignature([a, b])) == hash(ConditionsSignature([b, a_copy]))
    assert ConditionsSignature([a, a]) != ConditionsSignature([a])
    assert ConditionsSignature([a]) != ConditionsSignature([a.negate()])


def test_d2_a_colliding_bucket_never_merges_different_condition_sets(forced_collisions):
    """D2: candidate hash を定数にしても、別の条件集合は別の key のまま。"""

    a = _eq(_param("param_1", 0), _const(1))
    b = _eq(_param("param_1", 0), _const(2))
    left, right = ConditionsSignature([a]), ConditionsSignature([b])

    assert left.fast == right.fast
    assert left != right
    table = {left: "a", right: "b"}
    assert len(table) == 2
    assert table[ConditionsSignature([_eq(_param("param_1", 0), _const(1))])] == "a"


def test_d2_combine_and_and_basis_do_not_depend_on_the_hash_prefilter(monkeypatch):
    """D2: `combine_and` / basis の結果は candidate hash を衝突させても同じ。"""

    conditions = [
        _eq(_param("param_1", 0), _const(1)),
        _slt(_param("param_2", 1), _const(5)),
        _eq(_param("param_1", 0), _const(1)),
        _eq(_param("param_3", 2), _const(9)),
    ]

    def _shape(result):
        return [(c.negated, condition_key(c)) for c in result]

    combined = Condition.combine_and(list(conditions))
    basis = ConditionSimplifier.build_object_centric_condition_basis(list(conditions))
    monkeypatch.setattr(structural, "candidate_hash", lambda _expr: b"\x01" * 16)
    collided_combined = Condition.combine_and(list(conditions))
    collided_basis = ConditionSimplifier.build_object_centric_condition_basis(list(conditions))

    assert condition_key(collided_combined) == condition_key(combined)
    assert _shape(collided_basis) == _shape(basis)
    assert len(basis) == 3


def test_d2_deep_distinct_conditions_are_no_longer_equal_through_a_truncated_key():
    """旧 signature（`condition_key(budget=256)` の tuple）は予算の外の違いを見落としていた。

    Issue #215 の後は `condition_key` 自身も予算の外を識別する（打ち切りは起きるが、key は
    別になる）。signature はそれとは独立に、bucket + 完全比較で区別すること。
    """

    left = Condition(_deep_chain(_param("param_1", 0), 300))
    right = Condition(_deep_chain(_param("param_2", 1), 300))
    old_left, old_right = condition_key(left, budget=256), condition_key(right, budget=256)
    assert key_contains_placeholder(old_left) and old_left != old_right

    assert ConditionSimplifier.object_centric_conditions_signature([left]) != (
        ConditionSimplifier.object_centric_conditions_signature([right])
    )


def test_d8_every_object_centric_signature_consumer_gets_a_conditions_signature(
    forced_collisions,
):
    """D8: signature の consumer（dict / set の key）は bucket + 完全比較を受け取る。"""

    from scripts.function_tracer_pcode.analysis.effects.expression_forms import (
        _impl__runtime_conditions_signature,
    )
    from scripts.function_tracer_pcode.semantics.transform.expander_support import (
        ExpandedValue,
    )

    a = [_eq(_param("param_1", 0), _const(1))]
    b = [_eq(_param("param_1", 0), _const(2))]
    for producer in (
        ConditionSimplifier.object_centric_conditions_signature,
        _impl__runtime_conditions_signature,
        lambda conds: ExpandedValue(_const(0), conds).get_condition_signature(),
    ):
        left, right = producer(a), producer(b)
        assert isinstance(left, ConditionsSignature)
        assert hash(left) == hash(right)  # 衝突を強制している
        assert left != right
        assert len({(left, "v"), (right, "v")}) == 2


def test_d8_the_formula_return_dedup_keys_on_the_object_centric_signature():
    """D8: `proof/formula/returns.py` の `seen_defs` は signature を set の key にする。"""

    source = (PACKAGE_ROOT / "proof" / "formula" / "returns.py").read_text(encoding="utf-8")
    assert "ConditionSimplifier.object_centric_conditions_signature(raw_conditions)" in source
    assert "seen_defs.add(dedup_key)" in source


# ---------------------------------------------------------------------------
# D4: solver query identity と oracle cache
# ---------------------------------------------------------------------------


def test_d4_a_cache_hit_does_not_build_the_script(monkeypatch, scoped):
    """D4: 同じ意味の query（別 object）は 2 回目に script を組まない。"""

    builds = _count_builds(monkeypatch)
    first = [_slt(_param("param_1", 0), _const(0)), _slt(_const(0), _param("param_1", 0))]
    again = [_slt(_const(0), _param("param_1", 0)), _slt(_param("param_1", 0), _const(0))]

    assert ConditionSMTOracle.conjunction_is_unsat(first) is True
    assert ConditionSMTOracle.conjunction_is_unsat(again) is True
    assert builds == [2]
    assert scoped.metrics.count("oracle.queries") == 1
    assert scoped.metrics.count("cache.oracle.verdict.hit") == 1


def test_d4_a_remembered_none_is_a_hit_and_stays_unknown(monkeypatch, scoped):
    """D4: solver の `unknown` を覚え、次は solver を呼ばずに `None` を返す。"""

    fake = _FakeZ3(answer="unknown", reason="timeout")
    monkeypatch.setattr(ConditionSMTOracle, "_z3", fake)
    builds = _count_builds(monkeypatch)
    conditions = [_slt(_param("param_1", 0), _const(3))]

    assert ConditionSMTOracle.conjunction_is_unsat(conditions) is None
    assert ConditionSMTOracle.conjunction_is_unsat(
        [_slt(_param("param_1", 0), _const(3))]
    ) is None
    assert fake.checks == 1
    assert builds == [1]
    assert scoped.metrics.count("oracle.unknown_hit") == 1
    assert scoped.metrics.count("oracle.timeouts") == 1


def test_d4_an_exception_is_not_remembered(monkeypatch, scoped):
    """例外（parse の失敗など）は判定ではないので覚えない（毎回 solver に聞き直す）。"""

    fake = _FakeZ3(raises=ValueError("boom"))
    monkeypatch.setattr(ConditionSMTOracle, "_z3", fake)
    conditions = [_slt(_param("param_1", 0), _const(3))]

    assert ConditionSMTOracle.conjunction_is_unsat(conditions) is None
    assert ConditionSMTOracle.conjunction_is_unsat(conditions) is None
    assert fake.checks == 2
    assert len(scoped.store.table(ConditionSMTOracle.VERDICT_TABLE)) == 0


@pytest.mark.parametrize(
    "left, right",
    [
        pytest.param(
            lambda: _slt(_param("param_1", 0, ref_index=0), _const(0)),
            lambda: _slt(_param("param_1", 0, ref_index=5), _const(0)),
            id="same-name-and-width-different-runtime-identity",
        ),
        pytest.param(
            lambda: _slt(_storage_param(0x2000), _const(0)),
            lambda: _slt(_storage_param(0x2008), _const(0)),
            id="different-storage",
        ),
        pytest.param(
            lambda: _slt(_param("param_1", 0), _const(0)),
            lambda: _slt(_param("param_1", 0), _const(0)).negate(),
            id="negated",
        ),
        pytest.param(
            lambda: _slt(_param("param_1", 0, size=4), _const(0, size=4)),
            lambda: _slt(_param("param_1", 0, size=8), _const(0, size=8)),
            id="width",
        ),
        pytest.param(
            lambda: _eq(Expression.unknown("opaque_a"), _const(0)),
            lambda: _eq(Expression.unknown("opaque_b"), _const(0)),
            id="unknown-declaration",
        ),
    ],
)
def test_d4_queries_that_differ_in_solver_meaning_are_different_identities(left, right):
    """D4: 構造・名前・幅が同じでも solver の意味が違えば別 query（I-4）。"""

    left_query, right_query = _query(left()), _query(right())
    assert left_query != right_query
    assert _query(left()) == left_query


def test_d4_structurally_equal_conditions_can_still_be_different_queries():
    """I-4: structural identity の一致は solver query identity の一致を意味しない。"""

    left = _slt(_param("param_1", 0, ref_index=0), _const(0))
    right = _slt(_param("param_1", 0, ref_index=5), _const(0))
    assert left.equals(right)
    assert _query(left) != _query(right)


def test_d4_the_render_context_is_part_of_the_identity():
    condition = _slt(_param("param_1", 0), _const(0))
    other = RenderContext(float_mode="uf", render_schema=ORACLE_RENDER_CONTEXT.render_schema)
    assert _query(condition) != _query(condition, context=other)


def test_d4_forced_digest_collisions_never_produce_a_hit(forced_collisions, scoped):
    """D4: 外側の fast・graph digest・candidate hash を全部衝突させても誤 hit 0。"""

    satisfiable = [_slt(_param("param_1", 0), _const(3))]
    contradiction = [_slt(_param("param_1", 0), _const(0)), _slt(_const(0), _param("param_1", 0))]
    assert _query(*satisfiable).fast == _query(*contradiction[:1]).fast

    assert ConditionSMTOracle.conjunction_is_unsat(contradiction) is True
    # 同じ bucket に居る別の query は、記憶した `True` を受け取らない
    assert ConditionSMTOracle.conjunction_is_unsat(satisfiable) is False
    assert scoped.metrics.count("cache.oracle.verdict.bucket_collision") >= 1
    assert ConditionSMTOracle.conjunction_is_unsat(list(reversed(contradiction))) is True


def test_d4_the_cache_is_looked_up_before_the_script_is_built(monkeypatch, scoped):
    """lookup が `_build_script` より前であること（記憶した値があれば組まない）。"""

    conditions = [_slt(_param("param_1", 0), _const(3))]
    cache_store(ConditionSMTOracle.VERDICT_TABLE, _query(*conditions), True)

    def _boom(cls, *_args, **_kwargs):
        raise AssertionError("script built despite a remembered verdict")

    monkeypatch.setattr(ConditionSMTOracle, "_build_script", classmethod(_boom))
    assert ConditionSMTOracle.conjunction_is_unsat(conditions) is True


# ---------------------------------------------------------------------------
# D12: objvar の canonical な割当と、旧 script との意味の一致
# ---------------------------------------------------------------------------


def test_d12_symbol_assignment_does_not_depend_on_input_or_encounter_order():
    p1, p2 = _param("param_1", 0), _param("param_2", 1)
    left = [_slt(p1, p2), _eq(p2, _const(3))]
    right = [_eq(_param("param_2", 1), _const(3)), _slt(_param("param_1", 0), _param("param_2", 1))]

    usable_left, script_left = ConditionSMTOracle._build_script(left)
    usable_right, script_right = ConditionSMTOracle._build_script(right)
    assert usable_left and usable_right
    assert script_left == script_right
    names = _query(*left).symbol_names
    assert sorted(names.values()) == ["objvar_0", "objvar_1"]


def test_d12_symbol_names_depend_only_on_the_identity_set():
    """`objvar_<n>` は symbol identity の canonical な順（条件の形や出会い順に依らない）。"""

    split = _query(_slt(_param("param_2", 1), _const(0)), _slt(_param("param_1", 0), _const(9)))
    joined = _query(_slt(_param("param_1", 0), _param("param_2", 1)))
    reversed_join = _query(_slt(_param("param_2", 1), _param("param_1", 0)))
    assert dict(split.symbol_names) == dict(joined.symbol_names) == dict(reversed_join.symbol_names)


def _old_style_script(conditions):
    """旧 `_build_script` の組み立てを写したもの（比較の基準）。

    symbol は `_iter_expression_nodes` の出会い順、assert は入力順、1 本は
    `_condition_to_smt`（書き換え → 描画 → 否定）の後で非 bool の式だけ bool 化する。
    """

    from scripts.function_tracer_pcode.core.render_smt import (
        expression_returns_bool,
        expression_smt_bit_width,
    )

    oracle = ConditionSMTOracle
    names = {}
    for condition in conditions:
        for node in oracle._iter_expression_nodes(condition.expression):
            if node.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
                identity = oracle._expression_identity_key(node)
                names.setdefault(identity, f"objvar_{len(names)}")
    asserts = []
    for condition in conditions:
        rendered = oracle._rewrite_expr_with_symbol_names(condition.expression, names).to_smt(
            float_mode="fp"
        )
        if condition.negated:
            rendered = f"(not {rendered})"
        if not expression_returns_bool(condition.expression):
            bits = max(1, int(expression_smt_bit_width(condition.expression) or 0))
            rendered = f"(not (= {rendered} (_ bv0 {bits})))"
        asserts.append(rendered)
    return names, asserts


def test_d12_assert_bodies_are_the_old_ones_up_to_symbol_renaming():
    """representation: assert の本体は旧実装と同じ（symbol 名の付け替えと並び順だけが違う）。

    否定された非 bool の条件の組み立て（否定してから bool 化）も旧実装のまま。
    """

    flag = _param("param_4", 3, size=1)
    conditions = [
        Condition(flag, True),
        Condition(Expression.binary_op("INT_AND", _param("param_1", 0), _const(1)), False),
        _slt(_param("param_2", 1), _param("param_1", 0)).negate(),
    ]
    usable, new_script = ConditionSMTOracle._build_script(conditions)
    assert usable
    old_names, old_asserts = _old_style_script(conditions)
    new_names = _query(*conditions).symbol_names
    rename = {old_names[identity]: new_names[identity] for identity in old_names}
    expected = sorted(_rename(text, rename) for text in old_asserts)
    actual = sorted(
        line[len("(assert "):-1] for line in new_script.splitlines() if line.startswith("(assert ")
    )
    assert actual == expected


@pytest.mark.parametrize(
    "build",
    [
        lambda: [_slt(_param("param_1", 0), _param("param_2", 1)), _eq(_param("param_2", 1), _const(3))],
        lambda: [
            _eq(_param("param_3", 2), _const(1)).negate(),
            _slt(_param("param_1", 0), _const(0)),
            _slt(_param("param_3", 2), _param("param_1", 0)),
        ],
        lambda: [
            _eq(
                Expression.memory(_param("param_1", 0, size=8), size=4),
                _param("param_2", 1),
            ),
            _slt(_param("param_2", 1), _const(10)),
        ],
    ],
)
def test_d12_old_and_new_scripts_have_the_same_meaning(build):
    """D12: 新しい script（canonical な symbol・順）と旧 script は、symbol を対応付けると同値。

    `(assert (xor F_old F_new))` が z3 で **UNSAT**（unknown / timeout は失敗）。
    """

    conditions = build()
    usable, new_script = ConditionSMTOracle._build_script(conditions)
    assert usable
    old_names, old_asserts = _old_style_script(conditions)
    new_names = _query(*conditions).symbol_names

    declarations = [line for line in new_script.splitlines() if line.startswith("(declare")]
    new_asserts = [line[len("(assert "):-1] for line in new_script.splitlines() if line.startswith("(assert ")]
    renamed = []
    for identity, old_name in old_names.items():
        new_name = new_names[identity]
        renamed.append(f"(define-fun old_{old_name} () (_ BitVec {_width_of(declarations, new_name)}) {new_name})")
    old_body = [
        _rename(expr, {old: f"old_{old}" for old in old_names.values()}) for expr in old_asserts
    ]
    script = "\n".join(
        declarations
        + renamed
        + [f"(assert (xor (and true {' '.join(old_body)}) (and true {' '.join(new_asserts)})))"]
    )
    solver = z3.Solver()
    solver.set("timeout", 10_000)
    solver.add(z3.parse_smt2_string(script))
    assert solver.check() == z3.unsat


def _width_of(declarations, name):
    for line in declarations:
        if line.startswith(f"(declare-const {name} "):
            return int(line.rsplit(" ", 1)[1].rstrip(")"))
    raise AssertionError(name)


def _rename(text, mapping):
    import re

    return re.sub(r"\bobjvar_\d+\b", lambda match: mapping.get(match.group(0), match.group(0)), text)


# ---------------------------------------------------------------------------
# CNF の literal の並べ替え key（共有された構造 key を木として辿らない）
# ---------------------------------------------------------------------------


def _shared_key(depth):
    key = ("param", "param_1", ("int", 0), 4)
    for _ in range(depth):
        key = ("binary", "INT_ADD", 4, key, key)
    return key


def _reference_term_sort_key(term):
    """memo 無しの旧実装（値の基準。浅い項にだけ使う）。"""

    if term is None:
        return ("none",)
    if isinstance(term, (str, int, bool, float)):
        return (type(term).__name__, term)
    return ("tuple", tuple(_reference_term_sort_key(item) for item in term))


def _reference_total(value):
    if isinstance(value, bool):
        return ("bool", value)
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, str):
        return ("str", value)
    return ("tuple", tuple(_reference_total(item) for item in value))


def test_cnf_literal_sort_key_is_unchanged_and_linear_on_a_shared_key(scoped):
    shallow = _shared_key(4)
    literal = ((shallow, "INT_EQUAL", ("const", ("int", 0), 4)), True)
    expected = (
        _reference_total(_reference_term_sort_key(shallow)),
        "INT_EQUAL",
        _reference_total(_reference_term_sort_key(("const", ("int", 0), 4))),
        True,
    )
    assert ConditionSimplifier._literal_sort_key(literal) == expected

    # 木にすると 2^22 要素（memo 無しなら数秒以上かかる深さ。memo ありは distinct 23 個）
    deep = _shared_key(22)
    started = time.perf_counter()
    first = ConditionSimplifier._literal_sort_key(((deep, "INT_EQUAL", 0), True))
    again = ConditionSimplifier._literal_sort_key(((deep, "INT_EQUAL", 0), False))
    assert time.perf_counter() - started < 1.0
    assert first[0] is again[0]  # 項 object ごとの memo（pair の scope の中）


# ---------------------------------------------------------------------------
# D11: rewrite identity（oracle の cache とは別の契約）
# ---------------------------------------------------------------------------


def _rewrite_of(condition, query):
    entry_index = query.order.index(0)
    graph = query.entries[entry_index].graph
    return RewriteIdentity.for_root(graph, query.mapping_items())


def test_d11_distinct_runtime_identities_are_rewritten_to_distinct_symbols(scoped):
    """D11: 構造・名前・幅が同じで runtime identity が違う A / B を混同しない。"""

    a = _param("param_1", 0, ref_index=0)
    b = _param("param_1", 0, ref_index=7)
    conditions = [_slt(a, _const(0)), _slt(_const(0), b)]
    usable, script = ConditionSMTOracle._build_script(conditions)
    assert usable
    names = _query(*conditions).symbol_names
    assert len(set(names.values())) == 2
    assert script.count("declare-const objvar_") == 2
    # A と B が別の symbol なので矛盾ではない
    assert ConditionSMTOracle.conjunction_is_unsat(conditions) is False


def test_d11_occurrence_order_does_not_change_the_rewrite(scoped):
    a, b = _param("param_1", 0), _param("param_2", 1)
    forward = [_slt(a, b)]
    backward = [_slt(_param("param_1", 0), _param("param_2", 1))]
    assert _rewrite_of(forward[0], _query(*forward)) == _rewrite_of(backward[0], _query(*backward))
    reordered = [_slt(_param("param_2", 1), _param("param_1", 0))]
    assert _query(*reordered) != _query(*forward)


def test_d11_the_same_nodes_with_different_edges_are_different_graphs():
    x, y = _param("param_1", 0), _param("param_2", 1)
    sub_xy = Condition(Expression.binary_op("INT_SLESS", x, y))
    sub_yx = Condition(Expression.binary_op("INT_SLESS", y, x))
    assert not root_query_graph(sub_xy.expression).same_as(root_query_graph(sub_yx.expression))

    shared = _param("param_1", 0)
    with_sharing = Expression.binary_op("INT_EQUAL", shared, shared)
    without_sharing = Expression.binary_op("INT_EQUAL", _param("param_1", 0), _param("param_1", 0))
    assert root_query_graph(with_sharing).distinct_node_count == 2
    assert root_query_graph(without_sharing).distinct_node_count == 3
    assert not root_query_graph(with_sharing).same_as(root_query_graph(without_sharing))


def test_d11_phi_condition_and_value_placement_are_part_of_the_graph():
    selector = Expression.binary_op("INT_EQUAL", _param("param_1", 0), _const(0))
    one, two = _const(1), _const(2)
    phi_a = Expression.phi([(Condition(selector, False), one), (Condition(selector, True), two)])
    phi_b = Expression.phi([(Condition(selector, False), two), (Condition(selector, True), one)])
    phi_c = Expression.phi([(Condition(selector, True), one), (Condition(selector, False), two)])
    graph_a = root_query_graph(Expression.binary_op("INT_EQUAL", phi_a, _const(1)))
    assert not graph_a.same_as(root_query_graph(Expression.binary_op("INT_EQUAL", phi_b, _const(1))))
    assert not graph_a.same_as(root_query_graph(Expression.binary_op("INT_EQUAL", phi_c, _const(1))))


def _shared_dag(depth):
    node = _param("param_1", 0)
    for _ in range(depth):
        node = Expression.binary_op("INT_ADD", node, node)
    return Expression.binary_op("INT_EQUAL", node, _const(0))


@pytest.mark.parametrize("depth", [40, 60, 80])
def test_d11_shared_dag_identity_is_linear_in_distinct_nodes(depth):
    """D11: 共有 DAG（木にすると 2^depth）でも生成と比較は distinct node + 辺に比例する。"""

    started = time.perf_counter()
    left = root_query_graph(_shared_dag(depth))
    right = root_query_graph(_shared_dag(depth))
    compared = left.same_as(right)
    elapsed = time.perf_counter() - started

    assert compared
    assert left.distinct_node_count == depth + 3
    assert left.graph.edge_count == 2 * depth + 2
    assert elapsed < 1.0
    query_left = _query(Condition(_shared_dag(depth)))
    assert query_left == _query(Condition(_shared_dag(depth)))
    assert RewriteIdentity.for_root(left, query_left.mapping_items()) == RewriteIdentity.for_root(
        right, query_left.mapping_items()
    )


def _with_payload(graph, index, **changes):
    nodes = list(graph.graph.nodes)
    nodes[index] = dataclasses.replace(nodes[index], **changes)
    return dataclasses.replace(graph, graph=dataclasses.replace(graph.graph, nodes=tuple(nodes)))


def test_d11_digest_collisions_at_every_level_still_detect_payload_differences():
    """D11: 外側・graph・NodeRecord の digest を衝突させても local payload / 辺の差で miss。"""

    base = root_query_graph(_slt(_param("param_1", 0), _const(3)).expression)
    const_changed = root_query_graph(_slt(_param("param_1", 0), _const(4)).expression)
    runtime_changed = root_query_graph(_slt(_param("param_1", 0, ref_index=9), _const(3)).expression)
    edge_changed = root_query_graph(_slt(_const(3), _param("param_1", 0)).expression)

    for other in (const_changed, runtime_changed, edge_changed):
        # graph digest も node の candidate digest も base と同じ値に揃える
        forged = dataclasses.replace(other, digest=base.digest)
        forged = dataclasses.replace(
            forged,
            graph=dataclasses.replace(
                forged.graph,
                nodes=tuple(
                    dataclasses.replace(node, candidate_digest=b"\x00" * 16)
                    for node in forged.graph.nodes
                ),
            ),
        )
        assert not base.same_as(forged)
        mapping = (("identity", "objvar_0"),)
        left = RewriteIdentity.for_root(base, mapping)
        right = dataclasses.replace(
            RewriteIdentity.for_root(forged, mapping),
            fast=left.fast,
            mapping_digest=left.mapping_digest,
        )
        assert left != right

    # payload を 1 node だけ書き換えた graph（digest はそのまま）も一致しない
    tampered = _with_payload(base, 0, local_payload=("binary", "INT_SLESS", 5))
    assert not base.same_as(tampered)
    tampered_edges = _with_payload(base, 0, ordered_edges=((("operand", 0), 2), (("operand", 1), 1)))
    assert not base.same_as(tampered_edges)


def test_d11_same_root_with_different_mappings_or_contexts_are_different_rewrites():
    graph = root_query_graph(_slt(_param("param_1", 0), _param("param_2", 1)).expression)
    identity_1 = graph.symbols[0][0]
    identity_2 = graph.symbols[1][0]
    mapping_a = ((identity_1, "objvar_0"), (identity_2, "objvar_1"))
    mapping_b = ((identity_1, "objvar_1"), (identity_2, "objvar_0"))
    other_context = RenderContext(float_mode="uf", render_schema=ORACLE_RENDER_CONTEXT.render_schema)

    assert RewriteIdentity.for_root(graph, mapping_a) != RewriteIdentity.for_root(graph, mapping_b)
    assert RewriteIdentity.for_root(graph, mapping_a) != RewriteIdentity.for_root(
        graph, mapping_a, render_context=other_context
    )
    assert RewriteIdentity.for_root(graph, mapping_a) == RewriteIdentity.for_root(graph, mapping_a)


def test_d11_a_mapping_digest_collision_does_not_merge_mappings(forced_collisions):
    graph = root_query_graph(_slt(_param("param_1", 0), _param("param_2", 1)).expression)
    identity_1 = graph.symbols[0][0]
    identity_2 = graph.symbols[1][0]
    left = RewriteIdentity.for_root(graph, ((identity_1, "objvar_0"), (identity_2, "objvar_1")))
    right = RewriteIdentity.for_root(graph, ((identity_1, "objvar_1"), (identity_2, "objvar_0")))
    assert left.mapping_digest == right.mapping_digest and left.fast == right.fast
    assert left != right


def test_d11_the_same_root_in_two_queries_is_rendered_with_each_querys_mapping(scoped):
    """root だけで書き換えを覚えると、2 本目の query に 1 本目の symbol 名が混ざる。"""

    shared = _slt(_param("param_2", 1), _const(5))
    first = [shared, _eq(_param("param_1", 0), _const(0))]
    second = [shared, _eq(_param("param_9", 8), _const(0))]
    names_first = _query(*first).symbol_names
    names_second = _query(*second).symbol_names
    identity_2 = root_query_graph(shared.expression).symbols[0][0]
    assert names_first[identity_2] != names_second[identity_2]

    _, script_first = ConditionSMTOracle._build_script(first)
    _, script_second = ConditionSMTOracle._build_script(second)
    assert f"(bvslt {names_first[identity_2]} " in script_first
    assert f"(bvslt {names_second[identity_2]} " in script_second
    assert scoped.metrics.count("cache.oracle.rewrite.hit") == 0

    # 同じ query をもう一度組めば書き換えは使い回す
    ConditionSMTOracle._build_script(list(second))
    assert scoped.metrics.count("cache.oracle.rewrite.hit") == 2


# ---------------------------------------------------------------------------
# cache の寿命（pair）
# ---------------------------------------------------------------------------


@pytest.mark.unscoped_condition_cache  # scope の外の挙動を確かめる（Issue #224）
def test_nothing_is_remembered_outside_a_pair_scope(monkeypatch):
    builds = _count_builds(monkeypatch)
    conditions = [_slt(_param("param_1", 0), _const(0)), _slt(_const(0), _param("param_1", 0))]
    assert active_condition_cache() is None
    assert ConditionSMTOracle.conjunction_is_unsat(conditions) is True
    assert ConditionSMTOracle.conjunction_is_unsat(conditions) is True
    assert builds == [2, 2]
    assert cache_lookup("any", _query(*conditions)) == (False, None)
    built = []
    root_memo("kind", conditions[0].expression, lambda root: built.append(root))
    root_memo("kind", conditions[0].expression, lambda root: built.append(root))
    assert len(built) == 2


@pytest.mark.unscoped_condition_cache  # scope の外の挙動を確かめる（Issue #224）
def test_each_scope_starts_empty_and_restores_the_outer_store():
    key = _query(_slt(_param("param_1", 0), _const(0)))
    with condition_cache_scope() as outer:
        cache_store("t", key, True)
        with condition_cache_scope() as inner:
            assert inner is not outer
            assert cache_lookup("t", key) == (False, None)
        assert active_condition_cache() is outer
        assert cache_lookup("t", key) == (True, True)
    assert active_condition_cache() is None


def test_the_root_memo_does_not_keep_a_root_alive(scoped):
    """root 単位の memo は式 object を生かし続けない（回収されたら entry も消える）。"""

    import gc
    import weakref

    root = _slt(_param("param_1", 0), _const(0)).expression
    alive = weakref.ref(root)
    root_query_graph(root)
    assert root_query_graph(root) is root_query_graph(root)
    del root
    gc.collect()
    assert alive() is None
    memo = scoped.store._roots.get("query_identity.root_graph")
    # 回収の callback は消す予定を積むだけで、次の読み書き（ここでは `len`）で片付く
    assert memo is None or len(memo) == 0
    entries = memo._entries.values() if memo is not None else ()
    assert all(entry[0]() is not None for entry in entries)


def test_the_root_memo_keeps_values_that_cannot_be_weakly_referenced(scoped):
    term = ("param", "param_1", ("int", 0), 4)
    built = []
    assert root_memo("kind", term, lambda root: built.append(root) or "v") == "v"
    assert root_memo("kind", term, lambda root: built.append(root) or "other") == "v"
    assert built == [term]


class _Weighted:
    """`cache_weight()` を持つ値（重みの上限の test 用）。"""

    def __init__(self, name, weight):
        self.name = name
        self.weight = weight

    def cache_weight(self):
        return self.weight

    def __hash__(self):
        return hash(self.name)

    def __eq__(self, other):
        return isinstance(other, _Weighted) and other.name == self.name


def test_a_table_keeps_the_newest_entries_within_its_weight_limit(scoped):
    table = condition_cache.IdentityTable("t", limit=100, weight_limit=30)
    for index in range(5):
        table.store(_Weighted(f"k{index}", 9), index)
    # 1 件 = key 9 + value 1 = 10。上限 30 なので新しい 3 件だけ残る（古い順に捨てる）
    assert len(table) == 3
    assert table.weight == 30
    assert [table.lookup(_Weighted(f"k{index}", 9))[0] for index in range(5)] == [
        False, False, True, True, True,
    ]
    assert scoped.metrics.count("cache.t.evicted") == 2


def test_a_table_does_not_keep_an_entry_heavier_than_its_limit(scoped):
    table = condition_cache.IdentityTable("t", limit=100, weight_limit=30)
    table.store(_Weighted("small", 4), "s")
    table.store(_Weighted("huge", 100), "h")
    assert table.lookup(_Weighted("huge", 100)) == (False, None)
    # 重すぎる 1 件が他を追い出さない
    assert table.lookup(_Weighted("small", 4)) == (True, "s")
    assert scoped.metrics.count("cache.t.too_large") == 1


def test_replacing_an_entry_keeps_the_weight_consistent(scoped):
    table = condition_cache.IdentityTable("t", limit=100, weight_limit=1000)
    for _ in range(10):
        table.store(_Weighted("same", 7), "v")
    assert len(table) == 1
    assert table.weight == 8
    table.clear()
    assert len(table) == 0 and table.weight == 0


def test_the_count_limit_still_evicts_the_oldest_first(scoped):
    table = condition_cache.IdentityTable("t", limit=2, weight_limit=10_000)
    for index in range(4):
        table.store(("key", index), index)
    assert [table.lookup(("key", index))[0] for index in range(4)] == [False, False, True, True]


def test_the_weight_of_a_container_counts_distinct_objects_in_linear_time():
    """入れ物の重みは distinct な入れ物の数（共有は 1 回）。木として展開しない。"""

    shared = ("leaf",)
    for _ in range(40):
        shared = (shared, shared)
    # 共有された入れ子 tuple（木なら 2**40 個）は distinct な 41 個
    assert condition_cache.cache_weight(shared) == 41
    assert condition_cache.cache_weight((_Weighted("a", 5), 1)) == 1 + 5
    assert condition_cache.cache_weight(None) == 1
    # 深い入れ子も数える（1 段だけ見て 1 にしない）
    nested = ()
    for index in range(100):
        nested = (nested, index)
    assert condition_cache.cache_weight(nested) == 101


def test_the_weight_of_a_string_grows_with_its_length():
    assert condition_cache.cache_weight("x") == 1
    assert condition_cache.cache_weight("x" * (10 * 1024)) == 11
    assert condition_cache.cache_weight(("x" * (4 * 1024), "y")) == 1 + 4


def test_identity_weights_count_the_graph_nodes_they_keep_alive():
    small = _slt(_param("param_1", 0), _const(0))
    large = _slt(_deep_chain(_param("param_1", 0), 30), _const(0))
    small_graph = root_query_graph(small.expression)
    large_graph = root_query_graph(large.expression)
    assert small_graph.cache_weight() == len(small_graph.node_payloads)
    assert large_graph.cache_weight() > small_graph.cache_weight()
    query = _query(small, large)
    assert query.cache_weight() == 1 + sum(entry.graph.cache_weight() for entry in query.entries)
    assert query.cache_weight() >= 1 + small_graph.cache_weight() + large_graph.cache_weight() - 1


def test_stored_query_identities_keep_a_bounded_number_of_graph_nodes_alive(monkeypatch, scoped):
    """root の式が捨てられても、key の中の graph が上限を越えて残らない（RSS 増の原因）。"""

    import gc

    monkeypatch.setattr(condition_cache, "DEFAULT_TABLE_WEIGHT_LIMIT", 500)
    for index in range(200):
        condition = _slt(_deep_chain(_param("param_1", 0), 20), _const(index))
        cache_store(ConditionSMTOracle.VERDICT_TABLE, _query(condition), True)
        del condition
    gc.collect()
    table = scoped.store.table(ConditionSMTOracle.VERDICT_TABLE)
    assert 0 < table.weight <= 500
    kept_nodes = sum(
        len(entry.graph.node_payloads) for key, _v, _w, _h in table._entries.values() for entry in key.entries
    )
    assert kept_nodes <= 500
    # 新しいものは引ける
    newest = _slt(_deep_chain(_param("param_1", 0), 20), _const(199))
    assert cache_lookup(ConditionSMTOracle.VERDICT_TABLE, _query(newest)) == (True, True)


def test_the_root_memo_is_bounded_by_weight_and_forgets_collected_roots(monkeypatch, scoped):
    import gc

    monkeypatch.setattr(condition_cache, "DEFAULT_ROOT_MEMO_WEIGHT_LIMIT", 20)
    roots = [_Weighted(f"r{index}", 1) for index in range(10)]
    for root in roots:
        root_memo("kind", root, lambda _root: _Weighted("value", 5))
    memo = scoped.store._roots["kind"]
    assert memo.weight <= 20
    assert len(memo) == 4
    assert scoped.metrics.count("memo.kind.evicted") == 6
    del roots[-1], root
    gc.collect()
    assert len(memo) == 3
    assert memo.weight == 15
    root_memo("kind", _Weighted("big", 1), lambda _root: _Weighted("value", 50))
    assert scoped.metrics.count("memo.kind.too_large") == 1


def test_reset_caches_clears_only_the_owners_tables(scoped):
    key = _query(_slt(_param("param_1", 0), _const(0)))
    cache_store(ConditionSMTOracle.VERDICT_TABLE, key, True)
    cache_store(ConditionSimplifier.IMPLIED_TABLE, key, True)
    cache_store("unrelated", key, True)
    ConditionSimplifier.reset_caches()
    assert cache_lookup(ConditionSMTOracle.VERDICT_TABLE, key) == (False, None)
    assert cache_lookup(ConditionSimplifier.IMPLIED_TABLE, key) == (False, None)
    assert cache_lookup("unrelated", key) == (True, True)


@pytest.mark.unscoped_condition_cache  # scope の外の挙動を確かめる（Issue #224）
def test_the_pair_boundary_gives_every_pair_a_fresh_cache_and_counters():
    """pair 境界が cache と計測の scope を開閉する（次の pair へ持ち越さない）。"""

    from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
        _analyses,
        _healthy_stage_plan,
        _run_pair,
    )
    from scripts.function_tracer_pcode.tests.unit.test_issue125_limitation_finalization import (
        _connector,
    )

    analysis1, analysis2 = _analyses()
    key = _query(_slt(_param("param_1", 0), _const(0)))
    seen = []

    def _analyze(self, name, timeout):
        store, metrics = active_condition_cache(), active_condition_metrics()
        seen.append((store, metrics, cache_lookup("t", key)))
        cache_store("t", key, name)
        metrics.note("probe")
        return analysis1 if name == "func1" else analysis2

    for connector in (_connector(), None, _connector()):
        _run_pair(analyze=_analyze, stage_plan=_healthy_stage_plan, connector=connector)
        assert active_condition_cache() is None
        assert active_condition_metrics() is None

    stores = [store for store, _metrics, _lookup in seen]
    assert all(store is not None for store in stores)
    # 1 pair の中（func1 → func2）は同じ store、pair が変われば新しい store
    assert stores[0] is stores[1] and stores[2] is stores[3] and stores[4] is stores[5]
    assert len({id(stores[0]), id(stores[2]), id(stores[4])}) == 3
    lookups = [lookup for _store, _metrics, lookup in seen]
    assert lookups == [(False, None), (True, "func1")] * 3


# ---------------------------------------------------------------------------
# 旧実装と比べた重い処理の回数（repeated equivalent query）
# ---------------------------------------------------------------------------


def test_repeated_equivalent_queries_build_one_script_and_call_the_solver_once(
    monkeypatch, scoped
):
    """同じ意味の query を 20 回（毎回別 object）: 旧実装は 20 回 script を組み z3 を呼んだ。"""

    builds = _count_builds(monkeypatch)
    rewrites = []
    original_rewrite = ConditionSMTOracle._rewrite_expr_with_symbol_names.__func__

    def _counting_rewrite(cls, expr, symbol_names, active=None, memo=None):
        if active is None and memo is None:
            rewrites.append(expr)
        return original_rewrite(cls, expr, symbol_names, active, memo)

    monkeypatch.setattr(
        ConditionSMTOracle, "_rewrite_expr_with_symbol_names", classmethod(_counting_rewrite)
    )
    for _ in range(20):
        conditions = [_slt(_param("param_1", 0), _const(0)), _slt(_const(0), _param("param_1", 0))]
        assert ConditionSMTOracle.conjunction_is_unsat(conditions) is True
    assert builds == [2]
    assert len(rewrites) == 2
    assert scoped.metrics.count("oracle.queries") == 1
    assert scoped.metrics.count("cache.oracle.verdict.hit") == 19


def test_repeated_root_objects_build_their_graph_once(scoped):
    condition = _slt(_param("param_1", 0), _const(0))
    for _ in range(10):
        SolverQueryIdentity.from_conditions([condition, condition.negate()])
    assert scoped.metrics.count("identity.root_graph_built") == 1


def test_simplifier_implication_answers_are_cached_on_the_query_identity(scoped):
    context = [_slt(_param("param_1", 0), _const(0))]
    goal = _slt(_param("param_1", 0), _const(5))
    assert ConditionSimplifier._condition_is_implied(goal, context) is True
    assert ConditionSimplifier._condition_is_implied(
        _slt(_param("param_1", 0), _const(5)), [_slt(_param("param_1", 0), _const(0))]
    ) is True
    assert scoped.metrics.count("cache.simplifier.implied.hit") == 1
    # 正規形の集合を渡した問いは別の key（空の集合で得た答えを流用しない）
    ConditionSimplifier._condition_is_implied(goal, context, {("x", "INT_EQUAL", "y", True)})
    assert scoped.metrics.count("cache.simplifier.implied.hit") == 1
    # owner の合計は表ごとの数の和（`structural_key_cache_*` の元）
    for event in ("hit", "miss"):
        assert scoped.metrics.count(f"cache_family.simplifier.{event}") == sum(
            scoped.metrics.count(f"cache.{table}.{event}")
            for table in (ConditionSimplifier.CONJUNCTION_UNSAT_TABLE, ConditionSimplifier.IMPLIED_TABLE)
        )


# ---------------------------------------------------------------------------
# D13: PR-105-B 用の計測（DPLL・oracle・cache）と結果 JSON
# ---------------------------------------------------------------------------


def test_d13_dpll_decisions_and_satisfiability_calls_are_counted(monkeypatch, scoped):
    monkeypatch.setattr(
        ConditionSimplifier, "_should_use_solver_reasoning", classmethod(lambda cls, conds: False)
    )
    a = Expression.binary_op("INT_EQUAL", _param("param_1", 0), _const(0))
    b = Expression.binary_op("INT_EQUAL", _param("param_2", 1), _const(0))
    either = Condition(Expression.binary_op("BOOL_OR", a, b))
    assert ConditionSimplifier._formula_is_unsat([either]) is False

    snapshot = scoped.metrics.snapshot()
    assert snapshot["counters"]["dpll.satisfiability_calls"] == 1
    assert snapshot["counters"]["dpll.decisions"] >= 1
    per_call = snapshot["distributions"]["dpll.decisions_per_call"]
    assert per_call["count"] == 1 and per_call["max"] == snapshot["counters"]["dpll.decisions"]


def _note_plan_counters(metrics):
    metrics.note("oracle.queries", 4)
    metrics.note("cache.oracle.verdict.hit", 2)
    metrics.note("cache.oracle.verdict.bucket_collision", 1)
    metrics.note("oracle.unknown_hit", 1)
    metrics.note("oracle.timeouts", 1)
    metrics.note("cache_family.simplifier.hit", 5)
    metrics.note("cache_family.simplifier.miss", 5)
    # 表ごとの数は要約に足さない（合計は表が数えた `cache_family.*`）
    metrics.note("cache.simplifier.implied.hit", 3)
    metrics.note("dpll.satisfiability_calls", 6)
    metrics.note("dpll.decisions", 9)
    metrics.observe("dpll.decisions_per_call", 7)


_PLAN_COUNTERS = {
    "structural_key_cache_hit": 5,
    "structural_key_cache_miss": 5,
    "condition_oracle_query": 4,
    "condition_oracle_cache_hit": 2,
    "condition_oracle_unknown_hit": 1,
    "condition_oracle_identity_miss_after_hash_hit": 1,
    "condition_oracle_timeout": 1,
    "condition_satisfiability_calls": 6,
    "condition_dpll_decisions": 9,
    "condition_dpll_decisions_per_call_max": 7,
}


def _bare_result(**changes):
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    result = EquivalenceResult(
        is_equivalent=None, function1_name="l", function2_name="r",
        binary1_name="L", binary2_name="R", solver_results=None,
    )
    for name, value in changes.items():
        setattr(result, name, value)
    return result


def _attach_output_diagnostics(result):
    from scripts.function_tracer_pcode.checker import output_preparation

    prepared = SimpleNamespace(plan=SimpleNamespace(to_diagnostic=lambda: {}))
    policy = SimpleNamespace(to_diagnostic=lambda: {})
    output_preparation._attach_budget_diagnostics(result, prepared, policy)


def test_d3_counters_reach_pairwise_debug_stats_under_the_plan_names(scoped):
    """D3: pair の要約が `pairwise_debug_stats` に計画 §6.B-1 の名前で載る（0 は載せない）。"""

    _note_plan_counters(scoped.metrics)
    result = _bare_result(pairwise_debug_stats={"existing_counter": 1})
    _attach_output_diagnostics(result)
    assert result.to_dict()["pairwise_debug_stats"] == {"existing_counter": 1, **_PLAN_COUNTERS}
    # 同じ snapshot から写すので、診断の counter と食い違わない
    counters = result.to_dict()["diagnostics"]["condition_simplify"]["counters"]
    assert counters["oracle.queries"] == _PLAN_COUNTERS["condition_oracle_query"]


def test_d3_nothing_is_added_outside_a_pair_scope():
    assert active_condition_metrics() is None
    result = _bare_result(pairwise_debug_stats={"existing_counter": 1})
    _attach_output_diagnostics(result)
    assert result.to_dict()["pairwise_debug_stats"] == {"existing_counter": 1}


def test_d3_stage_merges_do_not_count_the_pair_totals_twice(scoped):
    """counter は pair の累計なので、出力で 1 回だけ写す（stage の合算に乗せない）。

    旧 head は結果の組み立て（stage / 再試行ごと）で累計を足し、stage の counter を
    合算する `merge_stage_debug_statistics` がそれをさらに足して数え過ぎた。
    """

    from scripts.function_tracer_pcode.checker.result_assembly import assemble_equivalence_result
    from scripts.function_tracer_pcode.proof.obligations.stage_runner import (
        merge_stage_debug_statistics,
    )

    _note_plan_counters(scoped.metrics)
    source = (PACKAGE_ROOT / "checker" / "result_assembly.py").read_text(encoding="utf-8")
    assert "condition_metrics" not in source and "pairwise_debug_counters" not in source
    assert assemble_equivalence_result  # 組み立ては counter を知らない

    accumulated = {}
    stages = [
        _bare_result(pairwise_debug_stats={"timeout_fallback_attempts": 1}),
        # 旧 head が書いていた stale な要約（stage ごとの累計）が残っていても上書きされる
        _bare_result(pairwise_debug_stats={"timeout_fallback_attempts": 2, "condition_oracle_query": 99}),
    ]
    for stage in stages:
        merge_stage_debug_statistics(accumulated, stage)
    final = stages[-1]
    _attach_output_diagnostics(final)
    stats = final.to_dict()["pairwise_debug_stats"]
    assert stats["timeout_fallback_attempts"] == 3
    assert {key: stats[key] for key in _PLAN_COUNTERS} == _PLAN_COUNTERS


def test_d13_counters_reach_the_result_json(scoped):
    """D13: 計測は出力の準備が診断へ写し、結果 JSON の `diagnostics.condition_simplify` に出る。"""

    from scripts.function_tracer_pcode.checker import output_preparation
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    scoped.metrics.note("oracle.queries", 3)
    scoped.metrics.observe("dpll.decisions_per_call", 5)
    result = EquivalenceResult(
        is_equivalent=None, function1_name="l", function2_name="r",
        binary1_name="L", binary2_name="R", solver_results=None,
    )
    result.diagnostics = {"failures": {"total": 0}}
    prepared = SimpleNamespace(plan=SimpleNamespace(to_diagnostic=lambda: {}))
    policy = SimpleNamespace(to_diagnostic=lambda: {})
    output_preparation._attach_budget_diagnostics(result, prepared, policy)

    block = result.to_dict()["diagnostics"]["condition_simplify"]
    assert block["schema"] == "condition-simplify-metrics-v1"
    assert block["counters"]["oracle.queries"] == 3
    assert block["distributions"]["dpll.decisions_per_call"]["max"] == 5
    assert result.to_dict()["diagnostics"]["failures"] == {"total": 0}


def test_d13_no_counters_outside_a_pair_scope_means_no_diagnostic_block():
    from scripts.function_tracer_pcode.checker import output_preparation

    assert active_condition_metrics() is None
    result = SimpleNamespace(diagnostics={})
    prepared = SimpleNamespace(plan=SimpleNamespace(to_diagnostic=lambda: {}))
    output_preparation._attach_budget_diagnostics(
        result, prepared, SimpleNamespace(to_diagnostic=lambda: {})
    )
    assert "condition_simplify" not in result.diagnostics


def test_d13_counters_do_not_change_answers(monkeypatch):
    """計測の scope があっても無くても答えは同じ（計測は判定に触れない）。"""

    conditions = [_slt(_param("param_1", 0), _const(0)), _slt(_const(0), _param("param_1", 0))]
    without = ConditionSimplifier.is_contradiction(list(conditions))
    with condition_metrics_scope():
        measured = ConditionSimplifier.is_contradiction(list(conditions))
    assert without is measured is True


# ---------------------------------------------------------------------------
# D9: 型名の表示は signature の field を書いたときに 1 回だけ（JVM の呼び出し）
# ---------------------------------------------------------------------------


def test_d9_attempt_records_do_not_call_the_type_name_again():
    from scripts.function_tracer_pcode.core.signature import FunctionSignature

    class _DataType:
        calls = 0

        def getName(self):
            type(self).calls += 1
            return "int"

    signature = FunctionSignature(return_type="int", return_type_obj=_DataType(), parameters=[])
    assert _DataType.calls == 1
    for _ in range(5):
        assert signature.to_dict()["return_type"] == "int"
        assert signature.format_return_type() == "int"
    assert _DataType.calls == 1


# ---------------------------------------------------------------------------
# 再発防止の契約（修正ラリーで後から見つかった種類の欠陥を、種類ごとに固定する）
# ---------------------------------------------------------------------------


class _Opaque:
    """式の値に入ると graph が比較できなくなる Python object。"""


def _uncacheable_condition():
    odd = Expression(ExpressionType.CONSTANT, value=_Opaque(), size=4)
    return Condition(Expression.binary_op("INT_EQUAL", _param("param_1", 0), odd))


def test_uncacheable_identities_are_equal_only_over_the_same_root_objects(scoped):
    """比較できない identity は同じ root object の上でだけ一致する（再入 guard 用）。

    旧 head は `self is other` のときしか一致せず、別々に作った同じ問いの identity が
    再入 guard の集合で見つからなかった（guard が効かない）。
    """

    condition = _uncacheable_condition()
    first = _query(condition)
    again = _query(condition)
    assert not first.cacheable
    assert first == again and hash(first) == hash(again)
    assert again in {first}
    # 構造が同じでも別の object は別（意味の一致とは言わない）
    assert _query(_uncacheable_condition()) != first
    # 向きが違えば別
    assert _query(condition.negate()) != first
    # 同じ object の多重集合なら入力順に依らない
    other = _uncacheable_condition()
    assert _query(condition, other) == _query(other, condition)


def test_tables_refuse_uncacheable_keys_in_one_place(scoped):
    condition = _uncacheable_condition()
    key = _query(condition)
    cache_store("t", key, True)
    assert cache_lookup("t", key) == (False, None)
    assert len(scoped.store.table("t")) == 0
    assert scoped.metrics.count("cache.t.uncacheable") == 1
    # consumer は判定を持たない（oracle も simplifier も表に任せる）
    for relative in ("analysis/condition/smt_oracle.py", "analysis/condition/simplifier.py",
                     "analysis/condition/simplifier_cnf.py"):
        text = (PACKAGE_ROOT / relative).read_text(encoding="utf-8")
        assert ".cacheable" not in text, relative


def test_the_reentry_guard_stops_an_uncacheable_conjunction(monkeypatch, scoped):
    """比較できない条件でも、同じ conjunction の判定の途中の再入は打ち切られる。"""

    calls = []
    condition = _uncacheable_condition()

    def _recursive(cls, condition_list):
        calls.append(len(condition_list))
        if len(calls) > 5:
            raise AssertionError("re-entry guard did not stop the recursion")
        return cls._conjunction_is_unsat([condition])

    monkeypatch.setattr(
        ConditionSimplifier, "_compute_conjunction_is_unsat", classmethod(_recursive)
    )
    assert ConditionSimplifier._formula_is_unsat([condition]) is None
    assert calls == [1]
    assert scoped.metrics.count("simplifier.reentry_guard_hit") == 1


def test_an_answer_built_on_a_reentry_guard_hit_is_not_remembered(monkeypatch, scoped):
    """再入 guard で打ち切った問いを材料にした答えは覚えない（evict / 呼ばれ方で答えが変わる）。"""

    outer = [_slt(_param("param_1", 0), _const(0))]
    inner = [_slt(_param("param_1", 0), _const(1))]
    original = ConditionSimplifier._compute_conjunction_is_unsat.__func__

    def _compute(cls, condition_list):
        if condition_list[0].equals(outer[0]):
            # outer の判定の途中で inner を聞き、inner の判定の途中で outer を聞く（再入）
            cls._conjunction_is_unsat(inner)
            return original(cls, condition_list)
        cls._conjunction_is_unsat(outer)
        return original(cls, condition_list)

    monkeypatch.setattr(
        ConditionSimplifier, "_compute_conjunction_is_unsat", classmethod(_compute)
    )
    assert ConditionSimplifier._formula_is_unsat(outer) is False
    table = ConditionSimplifier.CONJUNCTION_UNSAT_TABLE
    # inner は outer の再入の打ち切りを材料にしたので覚えない、outer もその inner を材料にしたので覚えない
    assert cache_lookup(table, _query(*inner)) == (False, None)
    assert cache_lookup(table, _query(*outer)) == (False, None)
    assert scoped.metrics.count("simplifier.guard_tainted_not_stored") == 2
    # 打ち切りの無い判定は覚える
    monkeypatch.setattr(
        ConditionSimplifier, "_compute_conjunction_is_unsat", classmethod(original)
    )
    assert ConditionSimplifier._formula_is_unsat(inner) is False
    assert cache_lookup(table, _query(*inner)) == (True, False)


def test_the_implication_cache_does_not_remember_a_guard_tainted_answer(monkeypatch, scoped):
    goal = _slt(_param("param_1", 0), _const(5))
    context = [_slt(_param("param_1", 0), _const(0))]

    def _reenter(cls, context_conditions, condition):
        # 含意の判定の途中で同じ含意を聞く（打ち切られて False）
        assert cls._condition_is_implied(goal, list(context)) is False
        return None

    monkeypatch.setattr(ConditionSimplifier, "_formula_implies", classmethod(_reenter))
    # 答え自体は scalar の含意で出る（p1 < 0 ⟹ p1 < 5）が、途中で再入を打ち切ったので覚えない
    assert ConditionSimplifier._condition_is_implied(goal, list(context)) is True
    key = query_identity.ImplicationIdentity.of(goal, context, None)
    assert cache_lookup(ConditionSimplifier.IMPLIED_TABLE, key) == (False, None)
    assert scoped.metrics.count("simplifier.guard_tainted_not_stored") == 1


def test_formula_is_unsat_and_formula_implies_share_one_owner_and_table(scoped):
    """文脈 ∧ ¬条件 の充足不能性は `_formula_is_unsat` と `_formula_implies` で同じ問い。"""

    context = [_slt(_param("param_1", 0), _const(0))]
    goal = _slt(_param("param_1", 0), _const(5))
    assert ConditionSimplifier._formula_implies(context, goal) is True
    assert ConditionSimplifier._formula_is_unsat(context + [goal.negate()]) is True
    assert scoped.metrics.count("cache.simplifier.conjunction_unsat.hit") == 1
    assert not hasattr(ConditionSimplifier, "FORMULA_UNSAT_TABLE")
    assert not hasattr(ConditionSimplifier, "FORMULA_IMPLIES_TABLE")


@pytest.mark.parametrize("site", ["oracle", "simplifier"])
def test_an_analysis_limitation_is_never_remembered(monkeypatch, scoped, site):
    from scripts.function_tracer_pcode.core.errors import AnalysisLimitation

    conditions = [_slt(_param("param_1", 0), _const(0))]
    limitation = AnalysisLimitation("analysis_budget_exceeded", "probe", site="test")
    fake = _FakeZ3(raises=limitation)
    monkeypatch.setattr(ConditionSMTOracle, "_z3", fake)
    monkeypatch.setattr(ConditionSMTOracle, "_available", True)
    monkeypatch.setattr(ConditionSMTOracle, "_availability_checked", True)
    call = (
        (lambda: ConditionSMTOracle.conjunction_is_unsat(conditions))
        if site == "oracle"
        else (lambda: ConditionSimplifier._formula_is_unsat(conditions))
    )
    with pytest.raises(AnalysisLimitation):
        call()
    # 判定の表（oracle の verdict・条件簡約の答え）には何も残らない。書き換えの表は
    # solver を呼ぶ前に作った描画（root と mapping だけで決まる値）なので対象外
    for name in (ConditionSMTOracle.VERDICT_TABLE, ConditionSimplifier.CONJUNCTION_UNSAT_TABLE,
                 ConditionSimplifier.IMPLIED_TABLE):
        assert len(scoped.store.table(name)) == 0, name


def test_answers_do_not_depend_on_eviction(monkeypatch):
    """同じ問いの列は、表が 1 件しか持てなくても・十分持てても同じ答えになる。"""

    def _questions():
        p1, p2 = _param("param_1", 0), _param("param_2", 1)
        atoms = [_slt(p1, _const(value)) for value in (0, 1, 5)] + [
            _eq(p2, _const(3)), _slt(_const(2), p1),
        ]
        answers = []
        for round_ in range(3):
            for left in atoms:
                for right in atoms:
                    answers.append(ConditionSimplifier._formula_is_unsat([left, right]))
                    answers.append(ConditionSimplifier._condition_is_implied(right, [left]))
                    answers.append(ConditionSMTOracle.conjunction_is_unsat([left, right.negate()]))
            atoms = [Condition(atom.expression, atom.negated) for atom in atoms]  # 別 object
        return answers

    with condition_cache_scope(), condition_metrics_scope():
        roomy = _questions()
    monkeypatch.setattr(condition_cache, "DEFAULT_TABLE_WEIGHT_LIMIT", 1)
    monkeypatch.setattr(condition_cache, "DEFAULT_ROOT_MEMO_WEIGHT_LIMIT", 1)
    with condition_cache_scope(), condition_metrics_scope() as metrics:
        cramped = _questions()
        assert metrics.count("cache.oracle.verdict.hit") == 0
    unscoped = _questions()
    assert roomy == cramped == unscoped


def test_oracle_symbols_and_declarations_come_from_one_traversal(monkeypatch, scoped):
    """`objvar` の割当（graph の symbol）と幅の宣言は同じ node の集合から来る。

    食い違ったら script を組まない（宣言の無い symbol を solver へ渡さない）。
    """

    from scripts.function_tracer_pcode.analysis.condition import smt_oracle

    conditions = [_slt(_param("param_1", 0), _param("param_2", 1))]
    usable, script = ConditionSMTOracle._build_script(conditions)
    assert usable and script.count("declare-const objvar_") == 2
    source = (PACKAGE_ROOT / "analysis" / "condition" / "smt_oracle.py").read_text(encoding="utf-8")
    facts_source = source[source.index("def _root_solver_facts"):source.index("def _merge_root_facts")]
    assert "walk_dag_nodes" in facts_source and "_iter_expression_nodes" not in facts_source

    original = smt_oracle._root_solver_facts

    def _drop_a_width(expr):
        facts = original(expr)
        return facts._replace(symbol_widths=facts.symbol_widths[:1])

    with condition_cache_scope():
        monkeypatch.setattr(smt_oracle, "_root_solver_facts", _drop_a_width)
        assert ConditionSMTOracle._build_script(conditions) == (False, None)
        assert ConditionSMTOracle.conjunction_is_unsat(conditions) is None


def test_the_weakref_callback_only_queues_the_entry_for_removal(scoped):
    """回収の callback は表を触らない（GC はどの bytecode の間でも走る）。次の読み書きで片付く。"""

    import gc

    root = _slt(_param("param_1", 0), _const(0)).expression
    root_memo("kind", root, lambda _root: "value")
    memo = scoped.store._roots["kind"]
    del root
    gc.collect()
    assert len(memo._entries) == 1 and len(memo._dead) == 1
    other = _slt(_param("param_1", 0), _const(9)).expression
    root_memo("kind", other, lambda _root: "other")
    assert len(memo._dead) == 0 and len(memo._entries) == 1


def test_a_strongly_held_root_counts_toward_the_memo_weight(monkeypatch, scoped):
    """弱参照を持てない root（tuple の構造 key）は memo が生かすので、その大きさも重みに入る。"""

    monkeypatch.setattr(condition_cache, "DEFAULT_ROOT_MEMO_WEIGHT_LIMIT", 50)
    big_term = ()
    for index in range(100):
        big_term = (big_term, index)
    root_memo("kind", big_term, lambda _root: 1)
    assert scoped.metrics.count("memo.kind.too_large") == 1
    assert len(scoped.store._roots["kind"]) == 0


def test_implication_identities_never_merge_under_forced_collisions(forced_collisions, scoped):
    goal = _slt(_param("param_1", 0), _const(5))
    context_a = [_slt(_param("param_1", 0), _const(0))]
    context_b = [_slt(_param("param_1", 0), _const(9))]
    key = query_identity.ImplicationIdentity.of(goal, context_a, None)
    cache_store("t", key, True)
    normed = query_identity.ImplicationIdentity.of(goal, context_a, {("a", "INT_EQUAL", "b", True)})
    cache_store("t", normed, False)
    # 正規形の集合が同じ大きさでも中身が違えば別の問い
    assert cache_lookup(
        "t", query_identity.ImplicationIdentity.of(goal, context_a, {("c", "INT_EQUAL", "d", True)})
    ) == (False, None)
    assert cache_lookup(
        "t", query_identity.ImplicationIdentity.of(goal, context_a, {("a", "INT_EQUAL", "b", True)})
    ) == (True, False)
    assert cache_lookup("t", query_identity.ImplicationIdentity.of(goal, context_a, None)) == (True, True)
    assert cache_lookup("t", query_identity.ImplicationIdentity.of(goal, context_b, None)) == (False, None)
    assert cache_lookup(
        "t", query_identity.ImplicationIdentity.of(goal.negate(), context_a, None)
    ) == (False, None)
