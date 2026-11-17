# -*- coding: utf-8 -*-
"""証明の前提の充足可能性の owner（Issue #298）。

EQ は「前提 ∧ 組の guard ∧ 値の不等式」が UNSAT であることを根拠にする。前提（header の
入力対応・型の仮説・FP の仮定・readonly の公理・global address、組の追加の assert）だけで
UNSAT なら、どの query も guard・値と無関係に UNSAT になる（空虚）。これを EQ の根拠に
しない。

区別するもの:

* **前提の矛盾**: 前提だけで UNSAT（または判定できない）。その比較の UNSAT は意味を持たない。
  解析の限界 ``proof_premise_unsatisfiable`` として pair の台帳へ記録し、確定判定へ進ませない
  （``core.errors.AnalysisLimitation``。記録が先、例外は後）。
* **正当に到達不能な組**: 前提は SAT で、guard を足して UNSAT になる組。これは引き続き EQ の
  根拠になる（ここでは何もしない）。

判定は SMT の結果だけで行う（前提の文字列は照合しない）。同じ前提は 1 回だけ解く。

この module は solver を持たない。query を解く関数を呼び手から受け取る。
"""

from __future__ import annotations

import hashlib
from typing import Callable, Dict, Iterable, Optional, Tuple

from scripts.function_tracer_pcode.core.errors import AnalysisLimitation, record_limitation

#: authority の契約上の reason id（``authority/domains/analysis_limitation.PROOF_PREMISE_UNSATISFIABLE_REASON_ID``
#: と同じ値。proof から authority を import しないので値を持つ。一致は test が固定する）。
PROOF_PREMISE_UNSATISFIABLE_REASON_ID = "proof_premise_unsatisfiable"
#: 限界を観測した場所
PROOF_PREMISE_LIMITATION_SITE = "proof.obligations.premise"
#: cause の target の名前
PROOF_PREMISE_TARGET = "proof_premise"

#: (label, query) を受け取り、SAT なら True・UNSAT なら False・決まらなければ None を返す関数
PremiseSolver = Callable[[str, str], Optional[bool]]


class ProofPremiseUnsatisfiable(AnalysisLimitation):
    """比較の前提が充足可能と示せない限界（その UNSAT を EQ の根拠にしない）。"""

    REASON_ID = PROOF_PREMISE_UNSATISFIABLE_REASON_ID

    def __init__(self, *, scope: str, status: Optional[bool], premise_digest: str) -> None:
        verdict = "unsat" if status is False else "undecided"
        super().__init__(
            self.REASON_ID,
            f"proof premise of {scope} is {verdict}",
            site=PROOF_PREMISE_LIMITATION_SITE,
            target_key=(PROOF_PREMISE_TARGET, scope),
            missing_semantic_fact=(PROOF_PREMISE_TARGET, "satisfiable"),
            evidence_refs=(f"premise_status={verdict}", f"premise_digest={premise_digest}"),
        )
        self.scope = scope
        self.status = status
        self.premise_digest = premise_digest


def require_satisfiable_premises(
    solve: PremiseSolver,
    premises: Iterable[Tuple[str, str]],
    *,
    cache: Optional[Dict[str, Optional[bool]]] = None,
) -> int:
    """全ての前提（``(scope, query)``）が SAT であることを確かめる。

    1 つでも UNSAT・判定不能なら、限界を台帳へ記録してから送出する。解いた（cache に無かった）
    query の数を返す。``cache`` は query → 結果（同じ比較の中で共有する）。
    """
    memo = cache if cache is not None else {}
    solved = 0
    for scope, query in premises:
        # 同じ前提かは query の文字列そのもので決める（digest は証拠の表示にだけ使う）
        if query in memo:
            status = memo[query]
        else:
            status = solve(scope, query)
            memo[query] = status
            solved += 1
        if status is not True:
            limitation = ProofPremiseUnsatisfiable(
                scope=scope,
                status=status,
                premise_digest=hashlib.sha256(query.encode("utf-8")).hexdigest(),
            )
            record_limitation(limitation)
            raise limitation
    return solved
