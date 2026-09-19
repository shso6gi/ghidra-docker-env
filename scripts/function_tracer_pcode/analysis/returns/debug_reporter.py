"""ReturnAnalyzer のデバッグ出力（lifecycle family から分割した横断 utility）。"""

from __future__ import annotations

from typing import Callable, Optional
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.analysis.debug import (
    summarize_expression,
    summarize_expression_details,
)


class DebugReporter:
    """デバッグ出力と式要約の collaborator。facade 状態のうち読むのは debug フラグのみ（supplier 経由）。

    lifecycle family の横断 utility（``_debug_print`` / ``_debug_expr_summary`` /
    ``_debug_expr_details_summary``）を切り出したもの。他の collaborator は本 class を直接依存として受け取る。

    ここが返す文字列はすべて診断専用の有界表示で、identity ではない。
    """

    def __init__(self, *, debug_flag: Callable[[], bool]) -> None:
        self.debug_flag = debug_flag

    def debug_available(self) -> bool:
        """debug 出力が有効か。

        returns family の debug guard の唯一の判定点。呼び出し側は message の
        組み立てごとこれで囲み、full render（``to_string`` / ``to_smt``）は
        使わずに ``summarize_expression`` 等の有界サマリーを渡す。
        """

        return bool(self.debug_flag())

    def debug_print(self, msg: str, indent: int = 0):
        if self.debug_flag():
            prefix = "  " * indent
            print(f"{prefix}[ReturnAnalyzer] {msg}")

    def debug_expr_summary(self, expr: Optional[Expression], max_depth: int = 4) -> str:
        return summarize_expression(expr, max_depth=max_depth)

    def debug_expr_details_summary(
        self,
        expr: Optional[Expression],
        max_depth: int = 3,
    ) -> str:
        """診断用の式詳細（有界）。identity ではないので判定に使わない。

        cache key / 等価判定 / digest / 証明の入力にしないこと
        （:func:`summarize_expression_details` の契約）。
        """

        return summarize_expression_details(expr, max_depth=max_depth)
