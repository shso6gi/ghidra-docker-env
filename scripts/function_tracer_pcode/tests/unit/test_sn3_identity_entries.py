# -*- coding: utf-8 -*-
"""Issue #215 (SN3) round 8: identity の **全入口** × schema の完全性 × 入れ子 × 凍結の前後。

identity の入口（記号の共有・identity の根拠になる値の入口）を列挙し、どの入口でも同じ契約が成り立つことを
確かめる。期待値は契約から決める（実装の出力を写さない）。

契約:

* 成分の欠けた schema（index の無い parameter など。`core/atom_validity.parameter_schema_complete`）・
  識別できない値を含む key は、**どの入口でも記号の共有の根拠にならない**: 生成 SMT の `distinct` の両辺は
  別の記号で、実際の `ConditionSMTOracle` は `x != y` を UNSAT と言わない（SAT か、使えないなら None）
* 完全な key は従来どおり: 同じ key の別の object は同じ記号（`x != x'` は UNSAT）、別の完全な key は
  別の記号（SAT）
* provenance key・構造 key・loop lowering の関数名でも、不完全・識別不能な key は等しくならない

入口（`semantic_projection._identity_of` が唯一の入口。下の表は、そこから値を受け取る経路）:

| 入口 | 記号 |
|---|---|
| VARIABLE / PARAMETER の runtime ref の `stable_key()` / `semantic_key()` | 条件 oracle の object 記号（`query_identity.solver_symbol_identity`） |
| index の無い PARAMETER の storage の `storage_identity_key()` | 同上（`parameter_storage`） |
| UNKNOWN の runtime ref の `stable_key()` / `semantic_key()` / origin | unknown 宣言の記号（`render_smt.unknowns`） |
| loop summary の Method B key | loop lowering の関数名（`runtime_lowering_identity`） |
| 上の全部 | provenance key（`structural.expression_provenance_key`） |
| runtime ref そのもの・`stable_key()` | 構造 key（`structural.expression_key_status`） |
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.analysis.condition.condition_cache import condition_cache_scope
from scripts.function_tracer_pcode.analysis.condition.query_identity import (
    solver_symbol_identity,
    solver_symbol_identity_is_safe,
)
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.core import semantic_projection as projection_module
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression
from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection
from scripts.function_tracer_pcode.core.structural import expression_key_status, unidentified_identity


# ---------------------------------------------------------------------------
# 値（契約の分類ごと）
# ---------------------------------------------------------------------------

_LAST = ("parameter", 1, 2, None)

#: 成分の欠けた schema（index の無い parameter）。最後の key は入れ子にも置く
INCOMPLETE = {
    "parameter_only": lambda: ("parameter",),
    "none_index": lambda: ("parameter", None),
    "none_width": lambda: ("parameter", 1, None),
    "none_index_4": lambda: _LAST,
    "in_tuple": lambda: ("wrap", _LAST),
    "in_dict": lambda: {"k": _LAST},
    "in_frozenset": lambda: frozenset({_LAST}),
}

_SHARED_TOKEN = unidentified_identity("unresolved")


class _Opaque:
    __slots__ = ()


#: 識別できない値（前の round の反例）
UNIDENTIFIED = {
    "shared_token": lambda: ("ref", _SHARED_TOKEN),
    "stateless_object": lambda: ("ref", _Opaque()),
}

#: 完全な key（別々の 2 つ）
COMPLETE = (lambda: ("loop", ("parameter", 1, 2, 3)), lambda: ("loop", ("parameter", 1, 2, 4)))


# ---------------------------------------------------------------------------
# 入口
# ---------------------------------------------------------------------------


class _Stable:
    __slots__ = ("key",)

    def __init__(self, key):
        self.key = key

    def stable_key(self):
        return self.key


class _Semantic:
    __slots__ = ("key",)

    def __init__(self, key):
        self.key = key

    def semantic_key(self):
        return self.key


class _Origin:
    __slots__ = ("key",)

    def __init__(self, key):
        self.key = key

    def stable_key(self):
        return self.key


class _OriginRef:
    __slots__ = ("origin_kind", "origin_ref")

    def __init__(self, key):
        self.origin_kind = "loop"
        self.origin_ref = _Origin(key)

    def stable_key(self):
        return ("same_for_all",)


class _Storage:
    __slots__ = ("key",)

    def __init__(self, key):
        self.key = key

    def storage_identity_key(self):
        return self.key


#: solver の記号を持つ入口（oracle まで通す）
SYMBOL_ENTRIES = {
    "variable_stable": lambda key: Expression(ExpressionType.VARIABLE, name="v", size=4, runtime_ref=_Stable(key)),
    "variable_semantic": lambda key: Expression(ExpressionType.VARIABLE, name="v", size=4, runtime_ref=_Semantic(key)),
    "parameter_semantic": lambda key: Expression(ExpressionType.PARAMETER, name=None, value=-1, size=4, runtime_ref=_Semantic(key)),
    "parameter_storage": lambda key: Expression(ExpressionType.PARAMETER, name=None, value=-1, size=4, storage_info=_Storage(key)),
    "unknown_stable": lambda key: Expression(ExpressionType.UNKNOWN, name="u", size=4, runtime_ref=_Stable(key)),
    "unknown_semantic": lambda key: Expression(ExpressionType.UNKNOWN, name="u", size=4, runtime_ref=_Semantic(key)),
    "unknown_origin": lambda key: Expression(ExpressionType.UNKNOWN, name="u", size=4, runtime_ref=_OriginRef(key)),
}


def _pair(entry, make, frozen):
    left, right = SYMBOL_ENTRIES[entry](make()), SYMBOL_ENTRIES[entry](make())
    if frozen:
        left, right = freeze_expression(left), freeze_expression(right)
    return left, right


def _notequal(left, right):
    condition = Condition(Expression.binary_op("INT_NOTEQUAL", left, right), False)
    ConditionSMTOracle.reset_caches()
    with condition_cache_scope():
        _usable, script = ConditionSMTOracle._build_script([condition])
        verdict = ConditionSMTOracle.conjunction_is_unsat([condition], use_cache=False)
    distinct = [line for line in (script or "").splitlines() if "distinct" in line]
    return verdict, distinct


def _shares_symbol(distinct):
    for line in distinct:
        body = line.replace("(assert (distinct ", "").rstrip(")").split()
        if len(body) == 2 and body[0] == body[1]:
            return True
    return False


# ---------------------------------------------------------------------------
# 記号の共有（全入口）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("entry", sorted(SYMBOL_ENTRIES))
@pytest.mark.parametrize("name", sorted(INCOMPLETE) + sorted(UNIDENTIFIED))
def test_no_entry_shares_a_symbol_on_an_incomplete_or_unidentified_key(name, entry, frozen):
    make = INCOMPLETE.get(name) or UNIDENTIFIED[name]
    left, right = _pair(entry, make, frozen)
    identity = solver_symbol_identity(left)
    assert identity is None or not solver_symbol_identity_is_safe(identity)
    verdict, distinct = _notequal(left, right)
    assert verdict is not True, distinct
    assert not _shares_symbol(distinct), distinct


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("entry", sorted(SYMBOL_ENTRIES))
def test_every_entry_keeps_legitimate_sharing_and_distinguishes_complete_keys(entry, frozen):
    same_left, same_right = _pair(entry, COMPLETE[0], frozen)
    verdict, distinct = _notequal(same_left, same_right)
    assert verdict is True, distinct
    assert _shares_symbol(distinct), distinct
    other = SYMBOL_ENTRIES[entry](COMPLETE[1]())
    if frozen:
        other = freeze_expression(other)
    verdict, distinct = _notequal(same_left, other)
    assert verdict is False, distinct
    assert not _shares_symbol(distinct), distinct


# ---------------------------------------------------------------------------
# provenance key・構造 key・loop lowering（記号以外の入口）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("entry", sorted(SYMBOL_ENTRIES))
@pytest.mark.parametrize("name", sorted(INCOMPLETE))
def test_an_incomplete_key_is_never_a_provenance_identity(name, entry, frozen):
    left, right = _pair(entry, INCOMPLETE[name], frozen)
    assert structural.expression_provenance_key(left) != structural.expression_provenance_key(right)
    projection = semantic_projection(left)
    if entry == "parameter_storage":
        assert projection.storage_identity is None and projection.storage_identity_unfixable
    else:
        assert projection.runtime_identity_unfixable is True


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("name", sorted(INCOMPLETE))
@pytest.mark.parametrize("direct", [True, False], ids=["direct_ref", "stable_key"])
def test_an_incomplete_key_never_makes_a_comparable_structural_key(name, direct, frozen):
    def build():
        ref = INCOMPLETE[name]() if direct else _Stable(INCOMPLETE[name]())
        expr = Expression(ExpressionType.UNKNOWN, name="u", size=4, runtime_ref=ref)
        return freeze_expression(expr) if frozen else expr

    left, right = build(), build()
    _key, comparable = expression_key_status(left)
    assert comparable is False
    assert structural.exact_structural_identity(left) != structural.exact_structural_identity(right)


class _Summary:
    __slots__ = ()

    def stable_key(self):
        return ("summary",)


class _LoopRef:
    __slots__ = ("loop_summary",)

    def __init__(self):
        self.loop_summary = _Summary()

    def stable_key(self):
        return ("loop_ref",)


@pytest.mark.parametrize("name", sorted(INCOMPLETE) + sorted(UNIDENTIFIED))
def test_an_unusable_method_b_key_never_names_a_shared_loop_function(name, monkeypatch):
    # loop summary の Method B key（`runtime_refs/loops.py` が組む）も `_identity_of` を通る
    make = INCOMPLETE.get(name) or UNIDENTIFIED[name]
    monkeypatch.setattr(projection_module, "loop_summary_method_b_key", lambda summary: make())
    left = freeze_expression(Expression(ExpressionType.UNKNOWN, name="u", size=4, runtime_ref=_LoopRef()))
    right = freeze_expression(Expression(ExpressionType.UNKNOWN, name="u", size=4, runtime_ref=_LoopRef()))
    assert semantic_projection(left).runtime_lowering_identity != semantic_projection(right).runtime_lowering_identity


def test_a_usable_method_b_key_still_names_one_shared_loop_function(monkeypatch):
    monkeypatch.setattr(projection_module, "loop_summary_method_b_key", lambda summary: ("method_b", ("parameter", 1, 2, 3)))
    left = freeze_expression(Expression(ExpressionType.UNKNOWN, name="u", size=4, runtime_ref=_LoopRef()))
    right = freeze_expression(Expression(ExpressionType.UNKNOWN, name="u", size=4, runtime_ref=_LoopRef()))
    assert semantic_projection(left).runtime_lowering_identity == semantic_projection(right).runtime_lowering_identity
    assert semantic_projection(left).runtime_lowering_identity[0] == "loop_summary_method_b_runtime"


# ---------------------------------------------------------------------------
# 入口の網羅（新しい identity の成分が `_identity_of` を通ること）
# ---------------------------------------------------------------------------


def test_every_projection_identity_component_goes_through_the_single_entry(monkeypatch):
    # projection が identity として持つ値（stable / semantic / origin / storage / Method B key）は、すべて
    # `_identity_of` を通る。入口を通らない成分を足すと、ここで数が合わなくなる
    seen = []
    original = projection_module._identity_of

    def spy(value):
        seen.append(value)
        return original(value)

    monkeypatch.setattr(projection_module, "_identity_of", spy)
    monkeypatch.setattr(projection_module, "loop_summary_method_b_key", lambda summary: ("method_b", 1))

    class _Everything:
        __slots__ = ("origin_kind", "origin_ref", "loop_summary")

        def __init__(self):
            self.origin_kind = "loop"
            self.origin_ref = _Origin(("origin", 1))
            self.loop_summary = _Summary()

        def stable_key(self):
            return ("stable", 1)

        def semantic_key(self):
            return ("semantic", 1)

    projection_module.project_runtime_ref(None, _Everything())
    projection_module.project_storage(_Storage(("storage", 1)))
    assert sorted(map(repr, seen)) == sorted(
        map(repr, [("stable", 1), ("semantic", 1), ("loop", ("origin", 1)), ("method_b", 1), ("storage", 1)])
    )


# ---------------------------------------------------------------------------
# identity の producer が情報を落とさないこと・粗い退避をしないこと（round 8 の反証レビュー）
# ---------------------------------------------------------------------------


def test_storage_identity_keeps_space_zero_apart_from_an_absent_space():
    # `int(space_id or -1)` は space 0（`register` の合成 id も 0）を「space が無い」と同じ値に畳んだ
    from scripts.function_tracer_pcode.core.storage import StorageInfo

    zero = StorageInfo(space_id=0, offset=8, size=4)
    absent = StorageInfo(offset=8, size=4)
    assert absent.space_id is None
    assert zero.storage_identity_key() != absent.storage_identity_key()
    assert zero.storage_identity_key() == StorageInfo(space_id=0, offset=8, size=4).storage_identity_key()
    register = StorageInfo(is_register=True, space_name="register", register_name="a1", base_register_name="a1",
                           base_register_offset=16, base_register_size_bits=64, size_bits=64, size=8)
    unknown_space = StorageInfo(is_register=True, register_name="a1", base_register_name="a1",
                                base_register_offset=16, base_register_size_bits=64, size_bits=64, size=8)
    assert register.space_id == 0 and unknown_space.space_id is None
    assert register.storage_identity_key() != unknown_space.storage_identity_key()


class _Keyless:
    __slots__ = ()


@pytest.mark.parametrize("kind", [ExpressionType.PARAMETER, ExpressionType.VARIABLE])
def test_a_keyless_ref_never_falls_back_to_an_index_or_name_symbol(kind):
    # key を出さない ref は identity を固定できない: index・名前の粗い identity へ退避しない（構造 key と同じ判断）
    def build():
        return freeze_expression(Expression(kind, name="p", value=0, size=4, runtime_ref=_Keyless()))

    left, right = build(), build()
    assert semantic_projection(left).runtime_identity_unfixable is True
    assert solver_symbol_identity(left) is None
    verdict, distinct = _notequal(left, right)
    assert verdict is not True, distinct
    assert not _shares_symbol(distinct), distinct
    assert structural.expression_provenance_key(left) != structural.expression_provenance_key(right)


def test_an_index_parameter_without_a_ref_still_shares_its_index_symbol():
    # 対照: ref を持たない PARAMETER は従来どおり index と名前で 1 つの記号（関数の parameter の対応）
    left = freeze_expression(Expression(ExpressionType.PARAMETER, name="p", value=0, size=4))
    right = freeze_expression(Expression(ExpressionType.PARAMETER, name="p", value=0, size=4))
    assert solver_symbol_identity(left) == ("parameter_index_name", 0, "p")
    verdict, distinct = _notequal(left, right)
    assert verdict is True, distinct
