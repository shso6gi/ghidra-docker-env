# -*- coding: utf-8 -*-
"""test が producer として意味値を公開するための入口。

本番では解析・proof の producer が「この値は確定した」と宣言してから consumer
（solver renderer / identity）へ渡す。式を自分で組み立てて renderer へ渡す test
は、その producer の役をしているので、同じ宣言を通す。

`expr.freeze()` では代わりにならない。凍結は「閉路が無く意味が確定した」ことしか
言っておらず、producer の宣言ではないので、凍らせただけの値は solver renderer に
拒否される（`core/semantic_lifecycle.py`）。ここを通すのは、test が producer の役を
していることを call site で読めるようにするため。
"""

from __future__ import annotations

from typing import Any

from scripts.function_tracer_pcode.core.semantic_freeze import publish


def published(value: Any) -> Any:
    """組み立て終えた意味値を公開して返す（本番の公開境界と同じ役）。"""

    return publish(value)


def published_raw_analysis(analysis: Any) -> Any:
    """組み立て終えた解析を、本番の解析の公開境界と同じく公開・封印して返す（Issue #185）。

    本番の raw 解析は ``analyze_function_by_name`` の公開境界で、意味値の公開と同時に
    parameter 表を入力領域の正本として封印される。fake の解析を raw 解析として比較へ
    渡す test は、表を組み終えた後（parameter を書き足す test はその後）でここを通す。
    """

    from scripts.function_tracer_pcode.core.analysis import publish_raw_function_analysis

    return publish_raw_function_analysis(analysis)


def raw_function_analysis(*args: Any, **kwargs: Any) -> Any:
    """``FunctionReturnAnalysis(...)`` を作り、raw 解析として入力領域を封印して返す（Issue #185）。

    raw 解析として比較へ渡す fake の解析用。parameter 表はこの時点の値が正本になるので、
    表を後から書き換える test は代わりに組み終えた後で ``published_raw_analysis`` を通す。
    意味値の公開はしない（元の test の組み立てどおり）。
    """

    from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis

    return FunctionReturnAnalysis(*args, **kwargs).seal_raw_parameter_domains()
