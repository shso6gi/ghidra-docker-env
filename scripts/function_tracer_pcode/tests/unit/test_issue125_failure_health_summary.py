# -*- coding: utf-8 -*-
"""typed failure 診断の run 集計（Issue #125 PR-125-B）。

PR-125-A が結果 JSON に書く `diagnostics["failures"]` を run 単位で集計し、
`result_summary --overall-summary` に 2 節（`Swallowed exceptions by type:` /
`Internal exceptions by site:`）として出す部分の契約を固定する。

固定する性質:

* 握り潰し例外を **型別 / site 別**に、内部エラーを **site 別**に数える。
* 複数 pair は加算される。1 pair の log に結果 payload が複数あっても
  最終結果だけを読む（同じ pair を二重に数えない）。
* `failures` block が無い log（PR-125-A 以前）でも落ちず、**「key が無い」を
  「0 件」と読ませない**（`(unknown)` と `(none)` を書き分ける）。
* 壊れた診断は件数に数えるだけで、summary 全体を落とさない（fail-open）。
* 新 2 節は parser を往復し、後続 section を飲み込まない。
* PR-128-A で確定した既存 section は 1 文字も変わらない。

診断は reporting 専用で、decision authority へは接続しない（その性質は
`test_issue125_typed_failures.py` が source で固定している）。
"""

from __future__ import annotations

import json
from types import SimpleNamespace

from scripts.function_tracer_pcode.checker.diagnostics import (
    FAILURE_INTERNAL_EXCEPTION,
    FAILURE_SWALLOWED_EXCEPTIONS,
    attach_failure_diagnostics,
    record_failure_diagnostic,
)
from scripts.function_tracer_pcode.core.errors import (
    InternalError,
    log_swallowed,
    reset_swallowed_exceptions,
)
from scripts.function_tracer_pcode.reporting.result_summary import (
    FAILURE_EVIDENCE_KEY,
    FAILURE_INTERNAL_BY_SITE_KEY,
    FAILURE_INTERNAL_BY_SITE_TITLE,
    FAILURE_SWALLOWED_BY_SITE_KEY,
    FAILURE_SWALLOWED_BY_TYPE_KEY,
    FAILURE_SWALLOWED_BY_TYPE_TITLE,
    FAILURE_SWALLOWED_TOTAL_KEY,
    aggregate_validation_logs_by_function,
    build_run_health_summary,
    format_failure_diagnostics_summary,
    format_overall_results_summary,
    format_run_health_summary,
    summarize_failure_diagnostics,
)
from scripts.function_tracer_pcode.reporting.run_health_summary import (
    parse_overall_summary_health,
)
from scripts.function_tracer_pcode.reporting.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


# ---------------------------------------------------------------------------
# fixture helpers
# ---------------------------------------------------------------------------


def _payload(function="f", failures=None, **extra):
    payload = {
        "function1_name": function,
        "function2_name": function,
        "binary1_name": "B1",
        "binary2_name": "B2",
        "is_equivalent": None,
    }
    if failures is not None:
        payload["diagnostics"] = {
            "schema": "result-diagnostics-v1",
            "failures": failures,
        }
    payload.update(extra)
    return payload


def _write_log(tmp_path, name, *payloads, human_result="Result: UNKNOWN"):
    path = tmp_path / name
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [human_result]
    for payload in payloads:
        lines.extend([RESULT_JSON_BEGIN, json.dumps(payload), RESULT_JSON_END])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def _records(tmp_path, *logs):
    return aggregate_validation_logs_by_function(logs).overall.records


def _producer_swallowed_block(entries):
    """PR-125-A の `attach_failure_diagnostics` が作る形そのものを使う。

    reporting 側が読む key を手書きの dict で固定すると producer 契約から
    ずれるので、実際の attach を通した payload を fixture にする。
    """

    reset_swallowed_exceptions()
    try:
        for reason_id, exc, site, count in entries:
            for _ in range(count):
                log_swallowed(reason_id, exc, site)
        result = SimpleNamespace(diagnostics=None)
        attach_failure_diagnostics(result)
        return dict(result.diagnostics["failures"])
    finally:
        reset_swallowed_exceptions()


def _producer_internal_block(site, exc):
    """`result_assembly.internal_error_result` が書く payload と同じ形。"""

    try:
        raise exc
    except type(exc) as raised:
        typed = InternalError(raised, site=site)
    result = SimpleNamespace(diagnostics=None)
    record_failure_diagnostic(result, FAILURE_INTERNAL_EXCEPTION, {
        "exception_type": typed.exception_type,
        "site": typed.site,
        "stack": list(typed.stack_lines()),
        "stack_digest": typed.stack_digest(),
    })
    return dict(result.diagnostics["failures"])


# ---------------------------------------------------------------------------
# 集計
# ---------------------------------------------------------------------------


def test_swallowed_exceptions_are_counted_by_type_and_by_site(tmp_path):
    failures = _producer_swallowed_block((
        ("return_width_bridge_missing", ValueError("a"), "analysis.returns.widths", 2),
        (None, KeyError("b"), "analysis.returns.widths", 1),
        (None, ValueError("c"), "semantics.normalize.fold", 3),
    ))
    assert failures[FAILURE_SWALLOWED_EXCEPTIONS]["total"] == 6

    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary = summarize_failure_diagnostics(_records(tmp_path, log))

    assert summary.swallowed_exception_total == 6
    assert summary.swallowed_exceptions_by_type == {"KeyError": 1, "ValueError": 5}
    assert summary.swallowed_exceptions_by_site == {
        "analysis.returns.widths": 3,
        "semantics.normalize.fold": 3,
    }
    assert summary.internal_exception_by_site == {}
    assert summary.results_observed == 1
    assert summary.results_missing == 0
    assert summary.malformed_results == 0


def test_internal_exceptions_are_counted_by_site(tmp_path):
    # 実 log では catch-all が `internal_exception` を書いたあとに
    # `attach_failure_diagnostics` が `swallowed_exceptions` を足す。
    left = _producer_internal_block(
        "checker.checker.EquivalenceChecker.check", RuntimeError("boom")
    )
    left.update(_producer_swallowed_block(()))
    right = _producer_internal_block(
        "analysis.returns.analyze_function", ValueError("other")
    )
    right.update(_producer_swallowed_block(((None, ValueError("x"), "proof.formula", 1),)))
    logs = (
        _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=left)),
        _write_log(tmp_path, "f/f_B1_B3.log", _payload(failures=right)),
        _write_log(tmp_path, "f/f_B1_B4.log", _payload(failures=left)),
    )
    summary = summarize_failure_diagnostics(_records(tmp_path, *logs))

    assert summary.internal_exception_by_site == {
        "analysis.returns.analyze_function": 1,
        "checker.checker.EquivalenceChecker.check": 2,
    }
    assert summary.swallowed_exceptions_by_type == {"ValueError": 1}
    assert summary.results_observed == 3


def test_multiple_pairs_add_up(tmp_path):
    logs = []
    for index in range(4):
        failures = _producer_swallowed_block(
            ((None, TypeError("t"), f"analysis.site{index % 2}", index + 1),)
        )
        logs.append(
            _write_log(tmp_path, f"f/f_B1_B{index + 2}.log", _payload(failures=failures))
        )
    summary = summarize_failure_diagnostics(_records(tmp_path, *logs))

    assert summary.swallowed_exception_total == 1 + 2 + 3 + 4
    assert summary.swallowed_exceptions_by_type == {"TypeError": 10}
    assert summary.swallowed_exceptions_by_site == {
        "analysis.site0": 1 + 3,
        "analysis.site1": 2 + 4,
    }


def test_zero_swallowed_exceptions_is_an_observed_zero(tmp_path):
    failures = _producer_swallowed_block(())
    assert failures[FAILURE_SWALLOWED_EXCEPTIONS] == {"by_site": [], "total": 0}

    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary = summarize_failure_diagnostics(_records(tmp_path, log))

    assert summary.results_observed == 1
    assert summary.results_missing == 0
    assert summary.swallowed_exception_total == 0
    assert summary.evidence_observed is True
    assert "(none)" in format_failure_diagnostics_summary(summary)
    assert "(unknown)" not in format_failure_diagnostics_summary(summary)


def test_logs_without_a_failures_block_are_missing_not_zero(tmp_path):
    """PR-125-A 以前の log。0 件と読ませず `(unknown)` にする。"""

    logs = (
        _write_log(tmp_path, "f/f_B1_B2.log", _payload()),
        _write_log(tmp_path, "f/f_B1_B3.log", _payload(diagnostics={"stages": {}})),
        _write_log(tmp_path, "f/f_B1_B4.log", human_result="Result: UNKNOWN"),
    )
    summary = summarize_failure_diagnostics(_records(tmp_path, *logs))

    assert summary.results_observed == 0
    assert summary.results_missing == 3
    assert summary.evidence_observed is False
    rendered = format_failure_diagnostics_summary(summary)
    assert f"{FAILURE_SWALLOWED_BY_TYPE_TITLE}:\n    (unknown)" in rendered
    assert f"{FAILURE_INTERNAL_BY_SITE_TITLE}:\n    (unknown)" in rendered


def test_mixed_old_and_new_logs_keep_both_counts(tmp_path):
    failures = _producer_swallowed_block(((None, OSError("io"), "ghidra.broker", 2),))
    logs = (
        _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures)),
        _write_log(tmp_path, "f/f_B1_B3.log", _payload()),
    )
    summary = summarize_failure_diagnostics(_records(tmp_path, *logs))

    assert (summary.results_observed, summary.results_missing) == (1, 1)
    assert summary.swallowed_exceptions_by_type == {"OSError": 2}
    # 1 件でも観測できていれば空の節は `(none)`（内部エラーは実際に 0 件）。
    assert f"{FAILURE_INTERNAL_BY_SITE_TITLE}:\n    (none)" in (
        format_failure_diagnostics_summary(summary)
    )


def test_only_the_final_payload_of_a_pair_is_counted(tmp_path):
    early = _producer_swallowed_block(((None, ValueError("early"), "analysis.a", 5),))
    final = _producer_swallowed_block(((None, ValueError("final"), "analysis.a", 1),))
    log = _write_log(
        tmp_path, "f/f_B1_B2.log", _payload(failures=early), _payload(failures=final)
    )
    summary = summarize_failure_diagnostics(_records(tmp_path, log))

    assert summary.results_observed == 1
    assert summary.swallowed_exception_total == 1


def test_malformed_failure_diagnostics_fail_open(tmp_path):
    good = _producer_swallowed_block(((None, ValueError("v"), "analysis.a", 2),))
    broken = (
        {"swallowed_exceptions": {"error": "RuntimeError: ledger unavailable"}},
        {"swallowed_exceptions": {"total": 3, "by_site": "not-a-list"}},
        {"swallowed_exceptions": {"total": 1, "by_site": [{"site": "s"}]}},
        {"swallowed_exceptions": {"total": 9, "by_site": []}},
        {
            "swallowed_exceptions": {"total": 0, "by_site": []},
            "internal_exception": "not-a-mapping",
        },
    )
    logs = [_write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=good))]
    for index, failures in enumerate(broken):
        logs.append(
            _write_log(
                tmp_path, f"f/f_B1_B{index + 3}.log", _payload(failures=failures)
            )
        )
    summary = summarize_failure_diagnostics(_records(tmp_path, *logs))

    assert summary.results_observed == 6
    assert summary.malformed_results == len(broken)
    # 読めた分だけは残る。壊れた行で全体を捨てない。
    assert summary.swallowed_exceptions_by_type == {"ValueError": 2}
    assert summary.swallowed_exception_total == 2


def test_a_failures_block_without_the_swallowed_ledger_is_malformed(tmp_path):
    """producer 契約では全 pair に `swallowed_exceptions` が載る。

    無い block は「観測できたが壊れている」として数え、内部エラーの site は
    読めた分だけ残す（欠けた key で pair ごと捨てない）。
    """

    failures = _producer_internal_block("checker.checker", RuntimeError("boom"))
    assert "swallowed_exceptions" not in failures
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary = summarize_failure_diagnostics(_records(tmp_path, log))

    assert summary.results_observed == 1
    assert summary.results_missing == 0
    assert summary.malformed_results == 1
    assert summary.internal_exception_by_site == {"checker.checker": 1}


def test_missing_site_or_type_uses_the_existing_missing_marker(tmp_path):
    failures = {
        "swallowed_exceptions": {
            "total": 2,
            "by_site": [{"site": None, "exception_type": None, "count": 2}],
        },
        "internal_exception": {"exception_type": "RuntimeError", "stack": []},
    }
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary = summarize_failure_diagnostics(_records(tmp_path, log))

    assert summary.swallowed_exceptions_by_type == {"<missing>": 2}
    assert summary.swallowed_exceptions_by_site == {"<missing>": 2}
    assert summary.internal_exception_by_site == {"<missing>": 1}
    assert summary.malformed_results == 0


# ---------------------------------------------------------------------------
# summary surface と parser
# ---------------------------------------------------------------------------


def _overall(tmp_path, *logs):
    summary = aggregate_validation_logs_by_function(logs)
    return summary, format_overall_results_summary(summary)


def test_overall_summary_carries_both_new_sections(tmp_path):
    failures = _producer_swallowed_block((
        (None, ValueError("v"), "analysis.a", 2),
        (None, KeyError("k"), "analysis.b", 1),
    ))
    failures.update(
        _producer_internal_block("checker.checker.EquivalenceChecker.check", OSError("x"))
    )
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    _summary, text = _overall(tmp_path, log)

    assert "  Failure diagnostics:" in text
    assert f"    {FAILURE_SWALLOWED_BY_TYPE_TITLE}:" in text
    assert f"    {FAILURE_INTERNAL_BY_SITE_TITLE}:" in text
    assert "      - ValueError: 2" in text
    assert "      - checker.checker.EquivalenceChecker.check: 1" in text
    # 新節は UNKNOWN block の後ろ、before/after delta の前。
    assert text.index("UNKNOWN validation summary:") < text.index("Failure diagnostics:")
    assert text.index("Failure diagnostics:") < text.index(
        "UNKNOWN validation before/after delta:"
    )


def test_new_sections_round_trip_through_the_health_parser(tmp_path):
    failures = _producer_swallowed_block((
        (None, ValueError("v"), "analysis.a", 2),
        (None, KeyError("k"), "analysis.b", 1),
    ))
    failures.update(_producer_internal_block("proof.strategies.pairwise", OSError("x")))
    logs = (
        _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures)),
        _write_log(tmp_path, "f/f_B1_B3.log", _payload()),
    )
    summary, text = _overall(tmp_path, *logs)
    path = tmp_path / "overall_summary.txt"
    path.write_text(text + "\n", encoding="utf-8")

    parsed = parse_overall_summary_health(path)
    built = build_run_health_summary(summary)

    assert parsed[FAILURE_SWALLOWED_BY_TYPE_KEY] == {"ValueError": 2, "KeyError": 1}
    assert parsed[FAILURE_INTERNAL_BY_SITE_KEY] == {"proof.strategies.pairwise": 1}
    assert parsed[FAILURE_EVIDENCE_KEY] == {"observed": 1, "missing": 1, "malformed": 0}
    assert parsed[FAILURE_SWALLOWED_TOTAL_KEY] == 3
    # structured summary は site 別の握り潰しも保持する（text には出さない次元）。
    assert built[FAILURE_SWALLOWED_BY_SITE_KEY] == {"analysis.a": 2, "analysis.b": 1}
    for key in (
        FAILURE_SWALLOWED_BY_TYPE_KEY,
        FAILURE_INTERNAL_BY_SITE_KEY,
        FAILURE_EVIDENCE_KEY,
        FAILURE_SWALLOWED_TOTAL_KEY,
    ):
        assert built[key] == parsed[key]


def test_new_sections_do_not_swallow_the_following_section(tmp_path):
    """新節の直後に来る既存 section の行を吸い込まないこと。"""

    path = tmp_path / "overall_summary.txt"
    path.write_text(
        "\n".join(
            [
                "  Overall totals              : TOTAL=  2, EQ=  1, NOT_EQ=  0,"
                " ERROR=  0, UNKNOWN=  1, TIMEOUT=  0, INCOMPLETE=  0",
                "  Failure diagnostics:",
                "    Results with failure diagnostics: 2 (missing 0, malformed 0)",
                "    Swallowed exceptions total: 3",
                f"    {FAILURE_SWALLOWED_BY_TYPE_TITLE}:",
                "      - ValueError: 3",
                f"    {FAILURE_INTERNAL_BY_SITE_TITLE}:",
                "      (none)",
                "    Operational UNKNOWN by reason:",
                "      - expression_semantics_unsupported: 7",
                "    UNKNOWN by reason:",
                "      - outcome_path_region_completeness_unproven: 9",
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    health = parse_overall_summary_health(path)

    assert health[FAILURE_SWALLOWED_BY_TYPE_KEY] == {"ValueError": 3}
    assert health[FAILURE_INTERNAL_BY_SITE_KEY] == {}
    assert health["operational_unknown_by_reason"] == {
        "expression_semantics_unsupported": 7
    }
    assert health["unknown_by_reason"] == {
        "outcome_path_region_completeness_unproven": 9
    }
    assert health["total_results"] == 2


def test_unknown_marker_round_trips_for_the_new_sections(tmp_path):
    logs = (_write_log(tmp_path, "f/f_B1_B2.log", _payload()),)
    summary, text = _overall(tmp_path, *logs)
    path = tmp_path / "overall_summary.txt"
    path.write_text(text + "\n", encoding="utf-8")

    health = parse_overall_summary_health(path)

    assert FAILURE_SWALLOWED_BY_TYPE_KEY in health["evidence_missing_sections"]
    assert FAILURE_INTERNAL_BY_SITE_KEY in health["evidence_missing_sections"]
    assert health[FAILURE_EVIDENCE_KEY] == {"observed": 0, "missing": 1, "malformed": 0}
    rendered = format_run_health_summary(health)
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (unknown)" in rendered
    assert f"  {FAILURE_INTERNAL_BY_SITE_KEY}:\n    (unknown)" in rendered
    # 観測できた run では同じ節が `(none)` で出る。
    observed = build_run_health_summary(
        aggregate_validation_logs_by_function(
            (
                _write_log(
                    tmp_path,
                    "g/g_B1_B2.log",
                    _payload(function="g", failures=_producer_swallowed_block(())),
                ),
            )
        )
    )
    observed_text = format_run_health_summary(observed)
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (none)" in observed_text


def test_a_pre_pr125b_summary_reads_as_unknown_not_zero(tmp_path):
    """PR-125-B 以前の `overall_summary.txt` / health JSON との後方互換。

    新 2 節が無い成果物を読んだときに「観測して 0 件」と言ってはいけない。
    """

    path = tmp_path / "overall_summary.txt"
    path.write_text(
        "\n".join(
            [
                "  Overall totals              : TOTAL=  2, EQ=  1, NOT_EQ=  0,"
                " ERROR=  0, UNKNOWN=  1, TIMEOUT=  0, INCOMPLETE=  0",
                "    UNKNOWN by reason:",
                "      - outcome_path_region_completeness_unproven: 1",
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    health = parse_overall_summary_health(path)

    assert health[FAILURE_EVIDENCE_KEY] == {}
    assert health[FAILURE_SWALLOWED_BY_TYPE_KEY] == {}
    assert health[FAILURE_SWALLOWED_TOTAL_KEY] == 0
    rendered = format_run_health_summary(health)
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (unknown)" in rendered
    assert f"  {FAILURE_INTERNAL_BY_SITE_KEY}:\n    (unknown)" in rendered
    # 既存 section の読み取りは壊れていない。
    assert health["unknown_by_reason"] == {
        "outcome_path_region_completeness_unproven": 1
    }
    # key を 1 つも持たない health（PR-125-B 以前の JSON）も同じ扱い。
    legacy = {"total_results": 2, "final_result_counts": {}, "unknown_units": 1}
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (unknown)" in (
        format_run_health_summary(legacy)
    )


def test_existing_summary_sections_are_unchanged_by_the_new_block(tmp_path):
    """新 block を取り除くと PR-128-A 時点の出力と 1 文字も変わらないこと。"""

    failures = _producer_swallowed_block(((None, ValueError("v"), "analysis.a", 1),))
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary, text = _overall(tmp_path, log)
    lines = text.splitlines()
    start = lines.index("  Failure diagnostics:")
    end = start
    while end < len(lines) and lines[end].strip():
        end += 1
    # block とその直後の空行 1 本だけを取り除く。
    without_new_block = "\n".join(lines[:start] + lines[end + 1:])

    # 既存 section は format_validation_unknown_summary / diff が作る。
    # そこへ入力も indent も変えずに渡していることを再構成で確認する。
    from scripts.function_tracer_pcode.reporting.unknown_reason_summary import (
        format_validation_unknown_diff_unavailable,
        format_validation_unknown_summary,
        summarize_validation_unknowns,
    )

    payloads = tuple(
        payload for record in summary.overall.records for payload in record.payloads
    )
    unknown_summary = summarize_validation_unknowns(payloads)
    expected_tail = "\n".join(
        [
            format_validation_unknown_summary(unknown_summary, indent="  "),
            "",
            format_validation_unknown_diff_unavailable(unknown_summary, indent="  "),
            "============================================================",
        ]
    )
    assert without_new_block.endswith(expected_tail)
    assert "Failure diagnostics:" not in without_new_block


def test_health_summary_json_keeps_the_three_planned_dimensions(tmp_path):
    failures = _producer_swallowed_block(((None, ValueError("v"), "analysis.a", 4),))
    failures.update(_producer_internal_block("smt.parallel.run_single", OSError("x")))
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    health = build_run_health_summary(aggregate_validation_logs_by_function((log,)))

    assert health[FAILURE_SWALLOWED_BY_TYPE_KEY] == {"ValueError": 4}
    assert health[FAILURE_SWALLOWED_BY_SITE_KEY] == {"analysis.a": 4}
    assert health[FAILURE_INTERNAL_BY_SITE_KEY] == {"smt.parallel.run_single": 1}
    assert health[FAILURE_SWALLOWED_TOTAL_KEY] == 4
    # 既存 key を落としていない。
    for key in (
        "unknown_by_reason",
        "proof_backlog_by_reason",
        "operational_unknown_by_reason",
        "error_kind_counts",
        "final_result_counts",
    ):
        assert key in health


def test_empty_run_renders_without_evidence_claims(tmp_path):
    summary = aggregate_validation_logs_by_function(())
    failure_summary = summarize_failure_diagnostics(summary.overall.records)

    assert failure_summary.results_observed == 0
    assert failure_summary.results_missing == 0
    text = format_overall_results_summary(summary)
    assert "Results with failure diagnostics: 0 (missing 0, malformed 0)" in text
