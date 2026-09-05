"""ReturnAnalyzer のデバッグ出力（lifecycle family から分割した横断 utility）。"""

from __future__ import annotations

from typing import Any, Callable, Optional
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.analysis.returns._shared import summarize_expression


class DebugReporter:
    """デバッグ出力と式要約の collaborator。facade 状態のうち読むのは debug フラグのみ（supplier 経由）。

    lifecycle family の横断 utility（``_debug_print`` / ``_debug_expr_summary`` /
    ``_debug_expr_identity_summary``）を切り出したもの。他の collaborator は本 class を直接依存として受け取る。
    """

    def __init__(self, *, debug_flag: Callable[[], bool]) -> None:
        self.debug_flag = debug_flag

    def debug_print(self, msg: str, indent: int = 0):
        if self.debug_flag():
            prefix = "  " * indent
            print(f"{prefix}[ReturnAnalyzer] {msg}")

    def debug_expr_summary(self, expr: Optional[Expression], max_depth: int = 4) -> str:
        return summarize_expression(expr, max_depth=max_depth)

    def debug_expr_identity_summary(
        self,
        expr: Optional[Expression],
        max_depth: int = 3,
    ) -> str:
        if expr is None:
            return "None"

        runtime_ref = getattr(expr, "runtime_ref", None)
        read_order_key = getattr(expr, "read_order_key", None)
        runtime_tag = type(runtime_ref).__name__ if runtime_ref is not None else "None"
        try:
            structural_key = expression_key_safe(
                expr,
                include_memory_read_order=True,
            )
        except Exception:
            structural_key = None
        return (
            f"{summarize_expression(expr, max_depth=max_depth)} "
            f"[type={expr.expr_type.name}, size={expr.size}, "
            f"read_order={read_order_key}, runtime_ref={runtime_tag}:{runtime_ref}, "
            f"structural={structural_key}]"
        )
