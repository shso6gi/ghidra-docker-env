# -*- coding: utf-8 -*-
"""`recorded-full` matrix の集計（Issue #109）。**replay は走らせない**。

各 shard は 1 replay だけを走らせ、すべての検査を通ったときだけ記録を 1 file
書く。ここはその file を集めて、corpus 全体としての契約だけを判定する:

* 期待した 9 variant が **ちょうど 1 回ずつ**現れる（欠落・重複・想定外は fail）
* 各 shard が成功している
* 合計時間が corpus budget 内

判定の実装は持たない。`tests/fixtures/pcode/corpus.validate_corpus` を呼ぶだけで、
serial 実行の集計と同じ規則・同じ code path を通る。

**artifact が無いことを「走らなくてよかった」と読まない。** shard は通ったときに
しか file を書かないので、file が無い = その replay は通っていない、であり、
ここは fail する。shard job の失敗を集計が隠すこともない。

budget は**各 replay の測定時間の合計**に掛ける。matrix で並列に流したときの
workflow wall-clock ではない（並列化は所要を短くするが、Issue #109 の時間 AC が
意味するものを変えない）。

これは test 基盤の report であって、checker にも判定 authority にも入力を渡さない。
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import List, Optional, Sequence

REPO_ROOT = Path(__file__).resolve().parents[4]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.function_tracer_pcode.tests.fixtures.pcode.corpus import (  # noqa: E402
    CORPUS_BUDGET_SECONDS,
    REPLAY_RECORD_SCHEMA,
    TIER_FULL,
    CorpusContractViolation,
    ReplayRecord,
    select_replays,
)


def read_records(reports_dir: Path) -> List[ReplayRecord]:
    """shard が書いた記録を集める。読めない file は黙って飛ばさない。"""

    records: List[ReplayRecord] = []
    paths = sorted(reports_dir.rglob("*.json"))
    for path in paths:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError) as exc:
            raise CorpusContractViolation(
                "a shard report could not be read ({}): {}".format(path, exc)
            ) from exc
        if not isinstance(payload, dict) or payload.get("schema") != (
            REPLAY_RECORD_SCHEMA
        ):
            raise CorpusContractViolation(
                "{} is not a recorded replay record; the aggregate refuses to "
                "guess which files count".format(path)
            )
        records.append(ReplayRecord.from_dict(payload))
    return records


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--reports-dir", required=True,
        help="directory holding the per-shard replay records (searched recursively)",
    )
    parser.add_argument(
        "--budget-seconds", type=int, default=CORPUS_BUDGET_SECONDS,
        help="corpus budget applied to the SUM of the replay times",
    )
    parser.add_argument(
        "--json", default=None,
        help="also write the aggregated records and total here",
    )
    args = parser.parse_args(argv)

    reports_dir = Path(args.reports_dir)
    if not reports_dir.is_dir():
        print(
            "the aggregate needs the shard reports, and {} is not a directory"
            .format(reports_dir), file=sys.stderr,
        )
        return 1

    expected = select_replays(tier=TIER_FULL)
    try:
        records = read_records(reports_dir)
        lines = validate(records, expected, args.budget_seconds)
    except CorpusContractViolation as violation:
        print("RECORDED CORPUS: FAIL", file=sys.stderr)
        print(str(violation), file=sys.stderr)
        return 1

    for line in lines:
        print(line)
    print("RECORDED CORPUS: PASS ({} of {} replays)".format(
        len(records), len(expected)
    ))
    if args.json:
        total = sum(record.seconds for record in records)
        Path(args.json).write_text(json.dumps({
            "schema": "recorded-corpus-aggregate-v1",
            "expected_replays": [spec.variant_id for spec in expected],
            "records": [record.to_dict() for record in records],
            "total_seconds": round(total, 3),
            "budget_seconds": args.budget_seconds,
            "budget_basis": "sum of the replay times, not workflow wall clock",
        }, ensure_ascii=False, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    return 0


def validate(records, expected, budget_seconds) -> List[str]:
    """集計の判定。規則は `corpus.validate_corpus` が 1 箇所で持つ。"""

    from scripts.function_tracer_pcode.tests.fixtures.pcode.corpus import (
        validate_corpus,
    )

    return validate_corpus(
        records, expected=expected, budget_seconds=budget_seconds,
    )


if __name__ == "__main__":
    sys.exit(main())
