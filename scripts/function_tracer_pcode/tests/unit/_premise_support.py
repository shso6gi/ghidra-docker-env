# -*- coding: utf-8 -*-
"""Test support（Issue #298）: stub の solver を使う test の証明の前提を「SAT」と明示する。

production は UNSAT を EQ の根拠にする前に、前提（header ∧ 組の追加の assert）だけの query を
``strategy._solve_premise_query`` で解く（``proof.obligations.premise``）。stub の solver は全ての
query に同じ答えを返すので、その答えを前提の query にも当てはめると、意図しない「前提の矛盾」に
なる。これらの test の合成の前提は充足可能なので、そのことをここで宣言する。前提の検査そのものは
``test_issue298_ub_path_binding.py`` が本物の solver で検査する。
"""

from __future__ import annotations

from typing import Any


def assume_satisfiable_premise(strategy: Any) -> Any:
    strategy._solve_premise_query = lambda scope, query: True
    return strategy
