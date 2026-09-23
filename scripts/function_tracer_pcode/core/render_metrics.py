# -*- coding: utf-8 -*-
"""process 内の描画観測の集計（診断専用）。

`core/render_output.RenderCounters` が 1 回分、こちらが pair process 全体分。
**判定にも authority にも使わない**。PR-22-D が予算の既定値を決めるときに
読む値で、この PR では「記録して読めるようにする」ところまで。

pair = process の前提（`docs` / runner）なので、集計は process 寿命で持ち、
pair の冒頭で `reset_render_metrics()` を呼べば 1 pair 分になる。solver worker
thread からも描画され得るので追記は lock で直列化する（counter だけの短い
critical section で、描画そのものは lock の外）。
"""

from __future__ import annotations

import threading
from typing import Any, Dict

from scripts.function_tracer_pcode.core.render_output import RenderCounters


_LOCK = threading.Lock()
_TOTALS = RenderCounters()


def record_render(counters: RenderCounters) -> None:
    """1 回分の観測を集計へ足す。"""

    with _LOCK:
        _TOTALS.merge(counters)


def render_metrics_snapshot() -> Dict[str, Any]:
    """集計の写し（呼び出し側が壊せない dict）。"""

    with _LOCK:
        return _TOTALS.as_dict()


def reset_render_metrics() -> None:
    """集計を 0 に戻す（pair の冒頭で呼ぶ）。"""

    global _TOTALS
    with _LOCK:
        _TOTALS = RenderCounters()
