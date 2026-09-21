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
