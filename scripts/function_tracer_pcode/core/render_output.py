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

上限の単位は **UTF-8 byte**（計画 v5 の `render_bytes`）。文字数ではないのは、
最終的に JSON へ出るのも solver へ渡るのも byte 列で、非 ASCII を含む symbol 名
では 1 文字が 1 byte とは限らないから。長さの数え方はこの module の
`utf8_length()` が唯一の owner で、renderer も出力口も同じ関数を使う。

上限は PR-22-C では既定 `None`（無効）。PR-22-D が `BudgetPolicy` からこの口へ
値を渡し、超過を登録済み reason の限界へ変換する。だから上限の **値** はここで
決めず、`limit_bytes` を受け取るだけにしてある。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional

from scripts.function_tracer_pcode.core.errors import AnalysisFailureError


def utf8_length(text: str) -> int:
    """`text` を UTF-8 で書いたときの byte 数（**長さの唯一の数え方**）。

    ASCII のときは文字数と同じなので、その場合は encode しない（描画は短い断片を
    大量に測るので、ここが素直な encode だと無視できない費用になる）。
    """

    return len(text) if text.isascii() else len(text.encode("utf-8"))


class RenderOutputLimitExceeded(AnalysisFailureError):
    """描画出力が上限に達した。

    `ValueError` / `TypeError` 派生にしない: 描画経路には
    `except (TypeError, ValueError, ...)` の回復 handler があり、そこへ吸われると
    「上限で打ち切った」が「その枝は描けなかった」に化けて、切り詰めた表現が
    solver へ流れ得る。PR-22-D がこの型を登録済み reason の
    `AnalysisLimitation` へ写す。
    """

    #: 上限の種類。`"output"` は出力量そのもの、`"material"` は renderer が抱える
    #: 材料の許容量（出力上限そのものではない）。1 つの field で両方を名乗ると、
    #: 受け取った側は `limit_bytes` が何の上限か分からない — 材料側は出力上限の
    #: 数倍になるので、そのまま「出力が N byte を超えた」と読むと誤る。
    OUTPUT = "output"
    MATERIAL = "material"

    def __init__(
        self,
        *,
        limit_bytes: int,
        requested_bytes: int,
        site: str,
        limit_kind: str = OUTPUT,
    ) -> None:
        super().__init__(
            f"render {limit_kind} exceeded {limit_bytes} bytes at {site} "
            f"(needed at least {requested_bytes})"
        )
        #: 超えた上限（`limit_kind` の上限）
        self.limit_bytes = int(limit_bytes)
        self.requested_bytes = int(requested_bytes)
        self.site = str(site)
        self.limit_kind = str(limit_kind)


class CountingWriter:
    """上限付きの追記口。断片を貯め、`getvalue()` で 1 回だけ連結する。

    `emitted_bytes` は書けた byte 数、`buffered_bytes` は **この口が同時に保持して
    いる** byte 数（`getvalue()` するまで貯まり続けるので、書き終わりでは
    `emitted_bytes` と等しい）。renderer 側の中間文字列の大きさは
    `RenderCounters.max_fragment_bytes` / `retained_fragment_bytes` が持つ —
    live memory は「この口の保持量 + renderer の保持量」で、片方だけを
    「peak」と呼ぶと実態とずれるので名前を分けてある。

    上限に達したら `RenderOutputLimitExceeded` を投げ、貯めた断片を捨てる
    （**完成文字列は作らない**）。
    """

    __slots__ = ("_parts", "_limit", "_site", "emitted_bytes", "part_count", "aborted")

    def __init__(self, *, limit_bytes: Optional[int] = None, site: str = "render") -> None:
        self._parts: List[str] = []
        self._limit = None if limit_bytes is None else int(limit_bytes)
        self._site = str(site)
        self.emitted_bytes = 0
        self.part_count = 0
        self.aborted = False

    @property
    def limit_bytes(self) -> Optional[int]:
        return self._limit

    @property
    def buffered_bytes(self) -> int:
        """この口が今まさに保持している byte 数。

        書いた分は貯めたままなので `emitted_bytes` と同じ値になり、打ち切った
        後だけ 0 になる（捨てるので）。断片を数え直さないのは、上限の判定と
        同じ数え方を 2 通り持ちたくないから。
        """

        return 0 if self.aborted else self.emitted_bytes

    def would_exceed(self, extra_bytes: int) -> bool:
        """`extra_bytes` を足したら上限を超えるか（書かずに確かめる）。"""

        if self._limit is None:
            return False
        return self.emitted_bytes + int(extra_bytes) > self._limit

    def reserve(self, extra_bytes: int) -> None:
        """見積り分の余地があるかを先に確かめる（無ければ打ち切り）。"""

        if self.would_exceed(extra_bytes):
            self._abort(int(extra_bytes))

    def write(self, text: str) -> None:
        if not text:
            return
        length = utf8_length(text)
        if self.would_exceed(length):
            self._abort(length)
        self._parts.append(text)
        self.emitted_bytes += length
        self.part_count += 1

    def write_repeated(self, text: str, count: int) -> None:
        """同じ断片を `count` 回。

        並びを組み立てる **前に** 全長を上限と比べる（`let` の閉じ括弧は入れ子の
        深さだけ並ぶので、深い式では無視できない長さになる）。上限があるとき、
        ここで作られる文字列は必ず上限以下。
        """

        count = int(count)
        if count <= 0 or not text:
            return
        self.reserve(utf8_length(text) * count)
        self.write(text * count)

    def getvalue(self) -> str:
        if self.aborted:
            return ""
        if len(self._parts) > 1:
            joined = "".join(self._parts)
            self._parts = [joined]
            return joined
        return self._parts[0] if self._parts else ""

    def _abort(self, requested_bytes: int) -> None:
        self.aborted = True
        # 途中まで貯めた断片も捨てる。ここで残すと「上限を超える文字列を
        # 作らない」という約束が、作ってから捨てるだけになる。
        self._parts = []
        raise RenderOutputLimitExceeded(
            limit_bytes=int(self._limit if self._limit is not None else 0),
            requested_bytes=int(requested_bytes),
            site=self._site,
            limit_kind=RenderOutputLimitExceeded.OUTPUT,
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
    #: node 本体を実行した回数（instance 数 + 子の解決による再実行 + 要求収集）
    node_body_executions: int = 0
    #: 本体へ子の項を渡した回数（幅の広い node の費用と、上限で止めた位置が見える）
    child_requests: int = 0
    #: 共有として名前を付けた instance 数
    shared_bindings: int = 0
    #: 共有名を参照した回数
    shared_references: int = 0
    #: PHI branch（case）を描いた回数
    case_count: int = 0
    #: 最終出力の byte 数
    emitted_bytes: int = 0
    #: renderer が作った **1 個の中間文字列**の最大長（= node 1 個分の fragment）
    max_fragment_bytes: int = 0
    #: renderer が同時に保持した中間文字列の総量（要求して捨てた子の分も含む）。
    #: 出力量の下界ではない — renderer が抱える材料の量（memory / 仕事の目安）
    retained_fragment_bytes: int = 0
    #: 木として展開したら幾つの node になったかの飽和付き見積り
    tree_node_estimate: int = 0

    def merge(self, other: "RenderCounters") -> None:
        """別の描画の観測を足し込む（最大値は最大、他は総和）。"""

        self.render_invocations += other.render_invocations
        self.distinct_rendered_nodes += other.distinct_rendered_nodes
        self.node_body_executions += other.node_body_executions
        self.child_requests += other.child_requests
        self.shared_bindings += other.shared_bindings
        self.shared_references += other.shared_references
        self.case_count += other.case_count
        self.emitted_bytes += other.emitted_bytes
        self.max_fragment_bytes = max(self.max_fragment_bytes, other.max_fragment_bytes)
        self.retained_fragment_bytes = max(
            self.retained_fragment_bytes, other.retained_fragment_bytes
        )
        self.tree_node_estimate = max(self.tree_node_estimate, other.tree_node_estimate)

    def as_dict(self) -> Dict[str, Any]:
        return {
            "render_invocations": self.render_invocations,
            "distinct_rendered_nodes": self.distinct_rendered_nodes,
            "node_body_executions": self.node_body_executions,
            "child_requests": self.child_requests,
            "shared_bindings": self.shared_bindings,
            "shared_references": self.shared_references,
            "case_count": self.case_count,
            "emitted_bytes": self.emitted_bytes,
            "max_fragment_bytes": self.max_fragment_bytes,
            "retained_fragment_bytes": self.retained_fragment_bytes,
            "tree_node_estimate": self.tree_node_estimate,
        }
