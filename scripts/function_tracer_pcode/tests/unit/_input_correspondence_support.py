# -*- coding: utf-8 -*-
"""Test support: mock FormulaBuilder が「渡された relation を報告する」ようにする（Issue #167）。

本物の ``FormulaBuilder.build_base_context`` / ``build_equivalence_formula_extended``
は、caller から受け取った最終 ``InputCorrespondenceSet`` で premise を描き、同じ
値を ``base_ctx["input_correspondence"]`` / ``FormulaBuilderResult.input_correspondence``
として返す。decisive gate はその値が strategy の relation と同じかを照合し、報告が
無ければ ``unavailable`` で fail-closed にする。

header を手で書いた mock builder を使う test（call effect / coverage / replay など
別の gate の test）は、この helper で本物と同じ報告契約だけを与える。premise の
正しさ自体は ``test_input_correspondence*.py`` が本物の builder で検証する。
"""

from __future__ import annotations

import dataclasses
from typing import Any

from scripts.function_tracer_pcode.proof.formula.types import FormulaBuilderResult


def echo_input_correspondence(builder: Any) -> Any:
    base_context = builder.build_base_context

    def build_base_context(*_args: Any, **kwargs: Any) -> Any:
        value = base_context.return_value
        if isinstance(value, dict):
            # 本物と同じく caller が後から書き足す dict そのものを返す（test が
            # 読み戻す key があるので複製しない）。
            value["input_correspondence"] = kwargs.get("input_correspondence")
        return value

    base_context.side_effect = build_base_context

    formula = builder.build_equivalence_formula_extended

    def build_formula(*_args: Any, **kwargs: Any) -> Any:
        value = formula.return_value
        if isinstance(value, FormulaBuilderResult) and value.input_correspondence is None:
            value = dataclasses.replace(value, input_correspondence=kwargs.get("input_correspondence"))
        return value

    formula.side_effect = build_formula
    return builder
