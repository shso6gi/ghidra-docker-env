# -*- coding: utf-8 -*-
"""記録済み corpus の replay（Issue #109）。**実行するだけの層**。

1 件の検証は `tests/fixtures/pcode/replay_validation.validate_replay` が
すべて持ち、この file はどれを走らせるかを決めて呼ぶだけ。PR gate の軽い 7
replay も、`recorded-full` workflow の 9 replay matrix も同じ関数を呼ぶので、
fast 専用 / full 専用の soundness 実装は存在しない。

どれを走らせるかは `cases.json` の `pr_gate` と明示の選択肢で決める。test 名への
`-k` 文字列一致には依存しない。

* 既定（`recorded-fast`）: `pr_gate` が true の replay
* `--recorded-tier=full`: 9 replay すべて（ローカルの通し実行用）
* `--recorded-replay=<variant_id>`（複数可）: その replay だけ（matrix の 1 shard）

`--recorded-report-dir` を渡すと、**すべての検査を通ったあとに**その replay の
記録を 1 file 書く。matrix の aggregate job はその file を読む。通らなければ
書かないので「file が無い＝その replay は通っていない」が成り立つ（aggregate は
それを fail として扱い、skip とは読まない）。

corpus 全体の完全性と 1200 秒予算は `tests/fixtures/pcode/corpus.validate_corpus`
が 1 箇所で持つ。serial 実行でも matrix 集計でも同じ実装が判定する。
"""

from __future__ import annotations

import importlib
import json
from pathlib import Path
from typing import Any, List, cast

pytest = cast(Any, importlib.import_module("pytest"))

from scripts.function_tracer_pcode.tests.fixtures.pcode.corpus import (
    CORPUS_BUDGET_SECONDS,
    ReplayRecord,
    TIER_FULL,
    format_summary,
    select_replays,
    validate_corpus,
)
from scripts.function_tracer_pcode.tests.fixtures.pcode.replay_validation import (
    validate_replay,
)

pytestmark = pytest.mark.recorded_replay

#: この実行で走った replay の記録。corpus 集計と報告のために貯める。
RECORDS: List[ReplayRecord] = []


def pytest_generate_tests(metafunc):
    """走らせる replay を manifest と明示の選択肢から決める。"""

    if "replay_spec" not in metafunc.fixturenames:
        return
    config = metafunc.config
    specs = select_replays(
        tier=config.getoption("recorded_tier"),
        variant_ids=tuple(config.getoption("recorded_replay")),
    )
    metafunc.parametrize(
        "replay_spec", specs, ids=[spec.variant_id for spec in specs],
    )


def test_recorded_pair(replay_spec, record_property, pytestconfig):
    record = validate_replay(replay_spec, record_property=record_property)
    RECORDS.append(record)

    report_dir = pytestconfig.getoption("recorded_report_dir")
    if report_dir:
        # 全検査を通ったあとにだけ書く。file の存在が「通った」と同義になる。
        directory = Path(report_dir)
        directory.mkdir(parents=True, exist_ok=True)
        (directory / (record.variant_id + ".json")).write_text(
            json.dumps(record.to_dict(), ensure_ascii=False, sort_keys=True),
            encoding="utf-8",
        )


def _write_lines(pytestconfig, lines) -> None:
    """pytest の terminal へ直接書く（capture を通らないので `-q` でも出る）。

    報告だけで、判定には関与しない。
    """

    reporter = None
    plugin_manager = getattr(pytestconfig, "pluginmanager", None)
    if plugin_manager is not None:
        reporter = plugin_manager.getplugin("terminalreporter")
    if reporter is None:  # pragma: no cover - terminal reporter の無い実行
        for line in lines:
            print(line)
        return
    reporter.ensure_newline()
    for line in lines:
        reporter.write_line(line)


def test_the_replays_that_ran_are_reported_and_within_budget(pytestconfig):
    """走った replay の所要を報告し、通し実行なら corpus 契約も判定する。

    完全性と 1200 秒予算は corpus 全体に対する契約なので、9 replay をそろえて
    走らせたときだけ適用する。PR gate（7 replay）や matrix の 1 shard で
    「合計が予算内だった」と言っても意味が無いし、部分集合の合計を AC の達成と
    読み替えてはいけない。matrix 実行の corpus 契約は aggregate job が
    **同じ** `validate_corpus` で判定する。

    所要は判定より先に出す。超過した run でしか数字が見えないと、今どれくらい
    なのかを報告するのに一度落とす必要が出てしまう。
    """

    selected = select_replays(
        tier=pytestconfig.getoption("recorded_tier"),
        variant_ids=tuple(pytestconfig.getoption("recorded_replay")),
    )
    full = select_replays(tier=TIER_FULL)
    is_whole_corpus = {spec.variant_id for spec in selected} == {
        spec.variant_id for spec in full
    }

    if not is_whole_corpus:
        _write_lines(pytestconfig, format_summary(RECORDS) + [
            "  (subset: {} of {} replays -- the {}s corpus budget is not "
            "claimed here; the recorded-full workflow's aggregate job applies "
            "it to all {})".format(
                len(RECORDS), len(full), CORPUS_BUDGET_SECONDS, len(full),
            ),
        ])
        return

    try:
        lines = validate_corpus(RECORDS, expected=full)
    except AssertionError:
        _write_lines(pytestconfig, format_summary(RECORDS))
        raise
    _write_lines(pytestconfig, lines)
