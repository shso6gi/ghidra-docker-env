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
    """D1: `analysis/condition/` の key・並べ替えに `repr` を使わない。

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
    """旧 signature（`condition_key(budget=256)` の tuple）は予算の外の違いを見落としていた。"""

    left = Condition(_deep_chain(_param("param_1", 0), 300))
    right = Condition(_deep_chain(_param("param_2", 1), 300))
    old_left, old_right = condition_key(left, budget=256), condition_key(right, budget=256)
    assert key_contains_placeholder(old_left) and old_left == old_right

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
    memo = scoped.store._roots.get("query_identity.root_graph", {})
    assert all(entry[0]() is not None for entry in memo.values())


def test_the_root_memo_keeps_values_that_cannot_be_weakly_referenced(scoped):
    term = ("param", "param_1", ("int", 0), 4)
    built = []
    assert root_memo("kind", term, lambda root: built.append(root) or "v") == "v"
    assert root_memo("kind", term, lambda root: built.append(root) or "other") == "v"
    assert built == [term]


def test_reset_caches_clears_only_the_owners_tables(scoped):
    key = _query(_slt(_param("param_1", 0), _const(0)))
    cache_store(ConditionSMTOracle.VERDICT_TABLE, key, True)
    cache_store(ConditionSimplifier.IMPLIED_TABLE, key, True)
    cache_store("unrelated", key, True)
    ConditionSimplifier.reset_caches()
    assert cache_lookup(ConditionSMTOracle.VERDICT_TABLE, key) == (False, None)
    assert cache_lookup(ConditionSimplifier.IMPLIED_TABLE, key) == (False, None)
    assert cache_lookup("unrelated", key) == (True, True)


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


def test_d3_counters_reach_pairwise_debug_stats_under_the_plan_names(scoped):
    """D3: pair の要約が `pairwise_debug_stats` に計画 §6.B-1 の名前で載る（0 は載せない）。"""

    from scripts.function_tracer_pcode.checker.result_assembly import _with_condition_counters

    scoped.metrics.note("oracle.queries", 4)
    scoped.metrics.note("cache.oracle.verdict.hit", 2)
    scoped.metrics.note("cache.oracle.verdict.bucket_collision", 1)
    scoped.metrics.note("oracle.unknown_hit", 1)
    scoped.metrics.note("oracle.timeouts", 1)
    scoped.metrics.note("cache.simplifier.implied.hit", 3)
    scoped.metrics.note("cache.simplifier.formula_implies.hit", 2)
    scoped.metrics.note("cache.simplifier.implied.miss", 5)
    scoped.metrics.note("dpll.satisfiability_calls", 6)
    scoped.metrics.note("dpll.decisions", 9)
    scoped.metrics.observe("dpll.decisions_per_call", 7)
    stats = _with_condition_counters({"existing_counter": 1})
    assert stats == {
        "existing_counter": 1,
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


def test_d3_nothing_is_added_outside_a_pair_scope():
    from scripts.function_tracer_pcode.checker.result_assembly import _with_condition_counters

    assert active_condition_metrics() is None
    original = {"existing_counter": 1}
    assert _with_condition_counters(original) is original
    assert _with_condition_counters(None) is None


def test_d3_the_result_assembly_uses_the_pair_summary():
    source = (PACKAGE_ROOT / "checker" / "result_assembly.py").read_text(encoding="utf-8")
    assert "pairwise_debug_stats=_with_condition_counters(strategy_result.pairwise_debug_stats)" in source


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
