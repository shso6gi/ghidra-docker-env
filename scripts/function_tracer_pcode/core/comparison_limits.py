# -*- coding: utf-8 -*-
"""比べる側の契約（`core/live_values`）の判定不能の意味の owner（Issue #242 第 8 回）。

`live_values` は標準 library だけを import するので、判定不能が「解析の限界」であること（pair の台帳へ記録し、
判定 authority の cause にすること）はここが決め、`live_values.register_undecidable_owner` で自分を登録する
（`core/read_limits` が読みの量の限界で同じことをする）。

判定不能（`ComparisonUndecidable`）は `core/errors.AnalysisLimitation` で、同時に `live_values.UndecidableComparison`:

- 作るときに pair の台帳へ記録する（記録が先、例外は後: `raise_limitation` と同じ規則）。途中の helper や
  `except Exception` が例外を握り潰しても、pair の境界は「判定不能があった」事実を読み、登録した reason
  （`comparison_undecidable`、`blocks_decision`）の cause にする。確定判定（EQ / NOT_EQ）には進まない。
- `TypeError` などの普通の例外の派生ではないので、「回復できる」例外の捕捉に吸収されない。
- 判定する側（`decided_equal` の 3 値・loop summary の比較の unknown）が局所で扱っても、台帳の事実は残る。

pair の外（unit test・台帳の無い呼び出し）では記録は何もしない（`core/errors.record_limitation` の規則）。
"""

from __future__ import annotations

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.errors import AnalysisLimitation, record_limitation

#: authority の契約上の reason id（`authority/domains/analysis_limitation.COMPARISON_UNDECIDABLE_REASON_ID` と同じ値）
COMPARISON_UNDECIDABLE_REASON_ID = "comparison_undecidable"
#: 限界を観測した場所（比べる側の契約）
COMPARISON_LIMITATION_SITE = "core.live_values.comparison"
#: cause の target の名前
COMPARISON_TARGET = "comparison"


class ComparisonUndecidable(AnalysisLimitation, live_values.UndecidableComparison):
    """比べる値を組み込みの code だけでは双子と同じに比べられない限界（判定しない）。"""

    REASON_ID = COMPARISON_UNDECIDABLE_REASON_ID

    def __init__(self, detail: str) -> None:
        detail = str.__str__(detail) if isinstance(detail, str) else "undecidable comparison"
        super().__init__(
            self.REASON_ID,
            detail,
            site=COMPARISON_LIMITATION_SITE,
            target_key=(COMPARISON_TARGET,),
            missing_semantic_fact=(COMPARISON_TARGET, "decidable_by_builtin_code"),
            evidence_refs=(f"detail={detail}",),
        )


def comparison_undecidable(detail: str) -> ComparisonUndecidable:
    """判定不能を pair の台帳へ記録してから返す（`live_values.undecidable` の owner。呼ぶ側が raise する）。"""

    limitation = ComparisonUndecidable(detail)
    record_limitation(limitation)
    return limitation


live_values.register_undecidable_owner(comparison_undecidable)
