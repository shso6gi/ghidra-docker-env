# -*- coding: utf-8 -*-
"""凍結違反と閉路が pair の結果になるまで（計画 B6 / B9）。

PR-106-0 は「内部バグをどう結果化するか」を作った。ここで固定するのは
**実際の producer**（`Expression.__setattr__` の凍結 guard と freeze 中の閉路
検出）が、その 1 本の経路にそのまま載ること。

consumer 側に閉路専用 / 凍結違反専用の catch を足さずに ERROR
`internal_exception` になることが要点で、逆に言えば新しい失敗の種類を足しても
gate も workflow も変えなくてよい、ということ。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core.errors import (
    ExpressionCycleError,
    FrozenExpressionError,
    current_pair_ledger,
    pair_failure_scope,
    reset_pair_failure_scopes,
)
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression, publish
from scripts.function_tracer_pcode.tests.unit.test_issue106_pair_limitation_propagation import (
    _analyses,
    _equivalent_stage_plan,
    _failure_block,
    _run_pair,
)
from scripts.function_tracer_pcode.tests.unit.test_issue125_limitation_finalization import (
    _connector,
)


@pytest.fixture(autouse=True)
def _clean_ledger_stack():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _cyclic_expression() -> Expression:
    """自分自身を operand に持つ式（通常入力としては認めない内部不整合）。"""

    node = Expression.unary_op("BOOL_NEGATE", Expression.constant(1, 1))
    node.__dict__["operands"] = [node]
    return node


# ---------------------------------------------------------------------------
# producer 単体
# ---------------------------------------------------------------------------


def test_freeze_records_the_cycle_in_the_ledger_before_raising():
    with pair_failure_scope(("bin1", "bin2"), None) as ledger:
        with pytest.raises(ExpressionCycleError):
            freeze_expression(_cyclic_expression())
        pending = ledger.pending_failure()
        assert pending is not None
        assert pending.is_internal_bug is True
        assert pending.site == "core.semantic_freeze.freeze_expression"


def test_frozen_mutation_records_the_bug_in_the_ledger_before_raising():
    expr = Expression.constant(1, 4)
    expr.freeze()
    with pair_failure_scope(("bin1", "bin2"), None) as ledger:
        with pytest.raises(FrozenExpressionError):
            expr.size = 8
        pending = ledger.pending_failure()
        assert pending is not None
        assert pending.is_internal_bug is True
        assert pending.site.startswith("core.semantic_freeze.frozen_mutation")


def test_a_cycle_is_not_rendered_into_a_proof():
    """閉路は公開の時点で落ち、solver renderer まで到達しない。"""

    with pytest.raises(ExpressionCycleError):
        publish(_cyclic_expression()).to_smt()


def test_a_swallowed_cycle_still_leaves_the_ledger_entry():
    with pair_failure_scope(("bin1", "bin2"), None) as ledger:
        try:
            freeze_expression(_cyclic_expression())
        except Exception:  # 深部の包括捕捉を再現する（test 側の模擬）
            pass
        assert ledger.pending_failure() is not None


# ---------------------------------------------------------------------------
# B6 / B9: pair の結果になるまで
# ---------------------------------------------------------------------------


def test_b6_a_cycle_during_analysis_becomes_an_internal_exception_error():
    analysis1, analysis2 = _analyses()

    def _analyze(self, name, timeout):
        if name == "func1":
            freeze_expression(_cyclic_expression())
        return analysis1 if name == "func1" else analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )

    assert result.is_equivalent is None
    assert result.failure_status == "internal_exception"
    assert result.final_outcome == "ERROR"
    failure = _failure_block(result, "internal_exception")
    assert failure["exception_type"] == "ExpressionCycleError"


def test_b9_a_frozen_mutation_behind_a_broad_except_becomes_an_error():
    """深い `except Exception: return None` 越しでも ERROR になる。"""

    analysis1, analysis2 = _analyses()
    frozen = Expression.constant(1, 4)
    frozen.freeze()

    def _analyze(self, name, timeout):
        if name == "func1":
            try:
                frozen.size = 8
            except Exception:  # 深部の包括捕捉を再現する（test 側の模擬）
                return None
        return analysis1 if name == "func1" else analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )

    assert result.failure_status == "internal_exception"
    assert result.final_outcome == "ERROR"
    failure = _failure_block(result, "internal_exception")
    assert failure["exception_type"] == "FrozenExpressionError"
    # 凍結された式は壊れていない。
    assert frozen.size == 4


def test_an_internal_bug_is_not_downgraded_to_unknown():
    analysis1, analysis2 = _analyses()
    frozen = Expression.constant(1, 4)
    frozen.freeze()

    def _analyze(self, name, timeout):
        if name == "func1":
            try:
                frozen.name = "x"
            except Exception:
                pass
        return analysis1 if name == "func1" else analysis2

    result = _run_pair(
        analyze=_analyze, stage_plan=_equivalent_stage_plan, connector=_connector(),
    )
    assert result.final_outcome == "ERROR"
    assert result.unknown_reasons == [] or result.failure_status == "internal_exception"


def test_no_ledger_scope_still_raises_the_typed_failure():
    """台帳の外（test が直接呼ぶ場合）でも型は同じで、黙って握らない。"""

    reset_pair_failure_scopes()
    assert current_pair_ledger() is None
    expr = Expression.constant(1, 4)
    expr.freeze()
    with pytest.raises(FrozenExpressionError):
        expr.size = 2
