# -*- coding: utf-8 -*-
"""比較の UB 除外の前提を、どこに課すかの owner（Issue #298）。

演算 o の UB 除外 ``ok(o)``（:class:`UbObligation`）は、o が実行される入力にだけ課す
（``exec(o) ⇒ ok(o)``）。経路への結び付け方は証明の方向で違う。

* **EQ の前提**（UNSAT を等価の証拠に使う query）: ``exec`` は実行を下から近似しなければ
  ならない（課した制約が UB の起きない入力を除くと偽 EQ になる）。ここでは比べている case の
  値と条件の中の演算だけを、その case の guard の下で課す（case の guard を assert した query
  では無条件の assert と同じ）。他の case の演算・経路を示せない演算の制約は課さない
  （前提を弱めるだけなので EQ に対して安全）。
* **反例の領域**（SAT の model を NOT_EQ の witness に使うとき）: ``exec`` は実行を上から
  近似しなければならない（witness の経路で実行される演算の UB を見落とさない）。ここでは
  関数全体の全ての演算の制約を無条件に課す（:meth:`UbPremise.witness_domain_lines`）。

さらに EQ の前提に課す obligation は、guard の領域を丸ごと除かないときだけ使う
（:func:`admissible_pair_obligations`）。guard だけでは到達できる case の組を UB 除外の
制約が空にするなら、その組の UNSAT は「UB 制約だけが入力を除いた」もので、EQ の根拠に
しない（obligation を外して比べ直す）。guard だけで到達不能な組は、その guard の query が
UNSAT を示すので、ここで区別しなくてよい。

この module は query の文字列を組まない。比べている case の obligation を集め、許可を
判断する入口を提供する。query への配置は ``proof/strategies/pairwise_query_builder.py``。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.proof.ub.constraints import (
    UbConstraintBuilder,
    UbObligation,
    analysis_expressions,
    obligation_lines,
)

#: base_ctx の中の置き場所（pairwise の query builder・executor・counterexample の検証が読む）。
UB_PREMISE_KEY = "ub_premise"
#: pair id → EQ の前提として許可した obligation の行（executor が書き、value query が読む）。
UB_PAIR_LINES_KEY = "ub_pair_obligation_lines"


def case_expressions(case: Any) -> List[Any]:
    """case の値と条件の式（その case の経路で実行される演算の範囲）。"""
    expressions: List[Any] = []
    value = getattr(case, "value_expr", None)
    if value is not None:
        expressions.append(value)
    for cond in getattr(case, "conditions", None) or ():
        expr = getattr(cond, "expression", None)
        if expr is not None:
            expressions.append(expr)
    return expressions


@dataclass
class UbPremise:
    """1 つの比較の UB 除外。側ごとの解析・引数表・記号の置換を持つ。"""

    builder: UbConstraintBuilder
    analyses: Dict[int, Any]
    param_infos: Dict[int, Sequence[Any]]
    symbol_replacers: Dict[int, Callable]
    _witness_lines: Optional[Tuple[str, ...]] = field(default=None, repr=False)

    def case_obligations(self, case: Any, side: int, replace_fn: Optional[Callable] = None) -> List[UbObligation]:
        """case の値と条件の中の演算の obligation（EQ の前提に使ってよいものだけ）。"""
        obligations = self.builder.collect_obligations(
            case_expressions(case),
            list(self.param_infos.get(side, ()) or ()),
            symbol_replace_fn=replace_fn or self.symbol_replacers.get(side),
        )
        return [obligation for obligation in obligations if obligation.eq_admissible]

    def pair_candidate_lines(
        self,
        case1: Any,
        case2: Any,
        replace_fn1: Optional[Callable] = None,
        replace_fn2: Optional[Callable] = None,
    ) -> Tuple[str, ...]:
        """比べる 2 つの case の obligation の行（許可の判断の前の候補）。"""
        obligations = self.case_obligations(case1, 1, replace_fn1) + self.case_obligations(
            case2, 2, replace_fn2
        )
        return tuple(obligation_lines(obligations))

    def witness_domain_lines(self) -> Tuple[str, ...]:
        """反例の領域: 両方の関数の全ての演算の制約を無条件に（実行を上から近似）。"""
        if self._witness_lines is None:
            lines: List[str] = []
            for side in (1, 2):
                analysis = self.analyses.get(side)
                if analysis is None:
                    continue
                lines.extend(
                    obligation_lines(
                        self.builder.collect_obligations(
                            analysis_expressions(analysis),
                            list(self.param_infos.get(side, ()) or ()),
                            symbol_replace_fn=self.symbol_replacers.get(side),
                        )
                    )
                )
            self._witness_lines = tuple(lines)
        return self._witness_lines


@dataclass(frozen=True)
class PairObligationDecision:
    """value query に課す obligation の判断（観測用の記録つき）。"""

    lines: Tuple[str, ...]
    verdict: str  # "none" | "admitted" | "region_excluded" | "region_undecided"


def admissible_pair_obligations(
    candidate_lines: Sequence[str],
    region_status: Callable[[Sequence[str]], Optional[bool]],
) -> PairObligationDecision:
    """候補の obligation を EQ の前提として許可するか決める。

    ``region_status(lines)`` は「比べる組の guard（と入力対応・pair の仮定）∧ lines」が
    充足可能なら True、充足不能なら False、決まらなければ None を返す。

    * 候補が無い: 何も課さない。
    * 充足可能: 課す（UB 制約はその組の入力の一部だけを除く。等価の証明に使ってよい）。
    * 充足不能: 課さない。guard だけで到達不能な組なら外しても結論は同じ。到達可能な組
      なら「UB 制約だけが入力を除いた」ので EQ の根拠にしない（外して比べ直す）。
    * 決まらない: 課さない（前提を弱める側に倒す）。
    """
    lines = tuple(candidate_lines)
    if not any(line.lstrip().startswith("(assert") for line in lines):
        return PairObligationDecision((), "none")
    status = region_status(lines)
    if status is True:
        return PairObligationDecision(lines, "admitted")
    if status is False:
        return PairObligationDecision((), "region_excluded")
    return PairObligationDecision((), "region_undecided")
