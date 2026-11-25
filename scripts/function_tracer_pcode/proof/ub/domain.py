# -*- coding: utf-8 -*-
"""反例の領域（UB を起こさない入力）の owner（Issue #298）。

NOT_EQ の witness は、どちらの関数の source でも UB を起こさない入力でなければならない
（#31: INT_MIN の負号を反例にしない）。binary からは source の演算・符号・実行条件を示せ
ないので、両方の関数の全ての演算の obligation（:mod:`proof.ub.constraints`。上から近似）を
経路の条件を付けずに課した領域に入る model だけを witness にする。

EQ の前提には UB の制約を課さない。P-code の演算は全ての入力で定義されていて、binary の
演算は source の UB の根拠にならない（課すと正当な入力を除いて偽 EQ になり得る）。

この module は query の文字列を組まない。領域の行を作るだけで、model の判定・領域の中での
解き直しは ``proof/strategies/pairwise_query_executor.py`` が行う。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.proof.ub.constraints import (
    UbConstraintBuilder,
    analysis_expressions,
    obligation_lines,
)

#: base_ctx の中の置き場所（counterexample の検証・解き直しが読む）。
UB_WITNESS_DOMAIN_KEY = "ub_witness_domain"


@dataclass
class UbWitnessDomain:
    """1 つの比較の反例の領域。側ごとの解析・引数表・記号の置換を持つ。"""

    builder: UbConstraintBuilder
    analyses: Dict[int, Any]
    param_infos: Dict[int, Sequence[Any]]
    symbol_replacers: Dict[int, Callable]
    _lines: Optional[Tuple[str, ...]] = field(default=None, repr=False)

    def lines(self) -> Tuple[str, ...]:
        """両方の関数の全ての演算の obligation を無条件に（描画の拒否はそのまま送出する）。"""
        if self._lines is None:
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
            self._lines = tuple(lines)
        return self._lines
