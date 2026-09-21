# -*- coding: utf-8 -*-
"""描画の **出力口** と計測値（renderer の出力側 owner）。

ここが持つのは 2 つだけ:

* `CountingWriter` — 「完成した文字列を作ってから長さを測る」をやめるための
  書き込み口。renderer は木を **流しながら**ここへ書くので、上限に届いた時点で
  それ以上は作られない。届いた時点で貯めた断片も捨てる。完成文字列を一度
  作ってしまうと、上限の意味が「作らせない」ではなく「作った後で捨てる」に
  なり、メモリと時間の保護にならない。
* `RenderCounters` — 1 回の描画で観測した量。**診断専用**で、判定にも
  authority にも使わない（PR-22-D が既定値を決めるための実測値）。

上限は PR-22-C では既定 `None`（無効）。PR-22-D が `BudgetPolicy` からこの口へ
上限を渡し、超過を登録済み reason の限界へ変換する。だから上限の値そのものは
ここでは決めず、`limit_chars` を受け取るだけにしてある。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional

from scripts.function_tracer_pcode.core.errors import AnalysisFailureError


class RenderOutputLimitExceeded(AnalysisFailureError):
    """描画出力が上限に達した。

    `ValueError` / `TypeError` 派生にしない: 描画経路には
    `except (TypeError, ValueError, ...)` の回復 handler があり、そこへ吸われると
    「上限で打ち切った」が「その枝は描けなかった」に化けて、切り詰めた表現が
    solver へ流れ得る。PR-22-D がこの型を登録済み reason の
    `AnalysisLimitation` へ写す。
    """

    def __init__(self, *, limit_chars: int, requested_chars: int, site: str) -> None:
        super().__init__(
            f"render output exceeded {limit_chars} chars at {site} "
            f"(needed at least {requested_chars})"
        )
        self.limit_chars = int(limit_chars)
        self.requested_chars = int(requested_chars)
        self.site = str(site)


class CountingWriter:
    """上限付きの追記口。断片を貯め、`getvalue()` で 1 回だけ連結する。

    `emitted_chars` は書けた文字数、`buffered_chars` は **この口が同時に保持して
    いる**文字数（`getvalue()` するまで貯まり続けるので、書き終わりでは
    `emitted_chars` と等しい）。renderer 側の中間文字列の大きさは
    `RenderCounters.max_fragment_chars` / `retained_fragment_chars` が持つ —
    live memory は「この口の保持量 + renderer の保持量」で、片方だけを
    「peak」と呼ぶと実態とずれるので名前を分けてある。

    上限に達したら `RenderOutputLimitExceeded` を投げ、貯めた断片を捨てる
    （**完成文字列は作らない**）。
    """

    __slots__ = ("_parts", "_limit", "_site", "emitted_chars", "part_count", "aborted")

    def __init__(self, *, limit_chars: Optional[int] = None, site: str = "render") -> None:
        self._parts: List[str] = []
        self._limit = None if limit_chars is None else int(limit_chars)
        self._site = str(site)
        self.emitted_chars = 0
        self.part_count = 0
        self.aborted = False

    @property
    def limit_chars(self) -> Optional[int]:
        return self._limit

    @property
    def buffered_chars(self) -> int:
        """この口が今まさに保持している文字数。"""

        return sum(len(part) for part in self._parts)

    def would_exceed(self, extra_chars: int) -> bool:
        """`extra_chars` を足したら上限を超えるか（書かずに確かめる）。"""

        if self._limit is None:
            return False
        return self.emitted_chars + int(extra_chars) > self._limit

    def reserve(self, extra_chars: int) -> None:
        """見積り分の余地があるかを先に確かめる（無ければ打ち切り）。"""

        if self.would_exceed(extra_chars):
            self._abort(int(extra_chars))

    def write(self, text: str) -> None:
        if not text:
            return
        length = len(text)
        if self.would_exceed(length):
            self._abort(length)
        self._parts.append(text)
        self.emitted_chars += length
        self.part_count += 1

    def write_repeated(self, text: str, count: int) -> None:
        """同じ断片を `count` 回。閉じ括弧の列を先に作らずに済ませる。"""

        count = int(count)
        if count <= 0 or not text:
            return
        self.reserve(len(text) * count)
        self.write(text * count)

    def getvalue(self) -> str:
        if self.aborted:
            return ""
        if len(self._parts) > 1:
            joined = "".join(self._parts)
            self._parts = [joined]
            return joined
        return self._parts[0] if self._parts else ""

    def _abort(self, requested_chars: int) -> None:
        self.aborted = True
        # 途中まで貯めた断片も捨てる。ここで残すと「上限を超える文字列を
        # 作らない」という約束が、作ってから捨てるだけになる。
        self._parts = []
        raise RenderOutputLimitExceeded(
            limit_chars=int(self._limit if self._limit is not None else 0),
            requested_chars=int(requested_chars),
            site=self._site,
        )


@dataclass
class RenderCounters:
    """1 回の描画で観測した量。**診断専用**（判定に使わない）。

    PR-22-D が `render_bytes` / `serialization_bytes` の既定値を決めるための
    実測値で、この PR では値を読むだけの利用者しか居ない。counter を判定に
    使い始めると、計測を足しただけで結果が動くようになる。
    """

    render_invocations: int = 0
    #: (node, render context) の組（= 描画 instance）の数
    distinct_rendered_nodes: int = 0
    #: node 本体を実行した回数（instance 数 + 子の解決による再実行）
    node_body_executions: int = 0
    #: 共有として名前を付けた instance 数
    shared_bindings: int = 0
    #: 共有名を参照した回数
    shared_references: int = 0
    #: PHI branch（case）を描いた回数
    case_count: int = 0
    #: 最終出力の文字数
    emitted_chars: int = 0
    #: renderer が作った **1 個の中間文字列**の最大長（= node 1 個分の fragment）
    max_fragment_chars: int = 0
    #: renderer が同時に保持した中間文字列の総量（fragment の合計）
    retained_fragment_chars: int = 0
    #: 木として展開したら幾つの node になったかの飽和付き見積り
    tree_node_estimate: int = 0

    def merge(self, other: "RenderCounters") -> None:
        """別の描画の観測を足し込む（最大値は最大、他は総和）。"""

        self.render_invocations += other.render_invocations
        self.distinct_rendered_nodes += other.distinct_rendered_nodes
        self.node_body_executions += other.node_body_executions
        self.shared_bindings += other.shared_bindings
        self.shared_references += other.shared_references
        self.case_count += other.case_count
        self.emitted_chars += other.emitted_chars
        self.max_fragment_chars = max(self.max_fragment_chars, other.max_fragment_chars)
        self.retained_fragment_chars = max(
            self.retained_fragment_chars, other.retained_fragment_chars
        )
        self.tree_node_estimate = max(self.tree_node_estimate, other.tree_node_estimate)

    def as_dict(self) -> Dict[str, Any]:
        return {
            "render_invocations": self.render_invocations,
            "distinct_rendered_nodes": self.distinct_rendered_nodes,
            "node_body_executions": self.node_body_executions,
            "shared_bindings": self.shared_bindings,
            "shared_references": self.shared_references,
            "case_count": self.case_count,
            "emitted_chars": self.emitted_chars,
            "max_fragment_chars": self.max_fragment_chars,
            "retained_fragment_chars": self.retained_fragment_chars,
            "tree_node_estimate": self.tree_node_estimate,
        }
