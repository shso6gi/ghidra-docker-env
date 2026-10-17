"""式から整数定数の値を取り出す collaborator。"""

from __future__ import annotations

from typing import Optional

from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType


class ConstantValueService:
    """ReturnAnalyzer の collaborator: ``CONSTANT`` の式の整数値（それ以外は ``None``）。

    状態も依存も持たない。ConditionLogicService / PlaceholderAlgebraService ほかが直接依存として使う。

    以前この service（旧 ``ConstantValueService``）は、base の key・定数・大きさの一致だけで比較を
    stack protector の照合と認め、return の条件から外していた（plan v4 PR-C で撤去）。形だけでは canary
    の照合と分からず（ふつうのコードの比較も一致する）、外すと機械語と違う関数を表すので、条件は残す。
    """

    def constant_int_value(self, expr: Optional[Expression]) -> Optional[int]:
        if expr is None or expr.expr_type != ExpressionType.CONSTANT:
            return None
        try:
            return int(expr.value)
        except (TypeError, ValueError):
            return None
