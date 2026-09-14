# -*- coding: utf-8 -*-
"""typed failure 診断の run 集計（Issue #125 PR-125-B）。

PR-125-A が結果 JSON に書く `diagnostics["failures"]` を run 単位で集計し、
`result_summary --overall-summary` に 2 節（`Swallowed exceptions by type:` /
`Internal exceptions by site:`）として出す部分の契約を固定する。

中心にあるのは **evidence 契約**（未観測を 0 件と読ませない）:

* evidence は **surface ごと**に持つ（握り潰し台帳 / 内部エラー）。
  片方が壊れても、もう片方の観測は有効なまま残す。
* `complete`（missing 0 / malformed 0）のときだけ、空集計を `(none)` と、
  合計を exact な整数と名乗れる。
* `partial` / `unknown` では空集計は `(unknown)`、合計は
  `unknown (observed N)` = **観測できた下限**として出す。
* partial でも、観測できた非 0 count は捨てない。

その他:

* 複数 pair は加算される。1 pair の log に結果 payload が複数あっても
  最終結果だけを読む（同じ pair を二重に数えない）。
* 壊れた診断は surface ごとに数えるだけで、summary 全体を落とさない。
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
    EVIDENCE_COMPLETE,
    EVIDENCE_PARTIAL,
    EVIDENCE_UNKNOWN,
    FAILURE_EVIDENCE_KEY,
    FAILURE_INTERNAL_BY_SITE_KEY,
    FAILURE_INTERNAL_BY_SITE_TITLE,
    FAILURE_INTERNAL_SURFACE,
    FAILURE_SWALLOWED_BY_SITE_KEY,
    FAILURE_SWALLOWED_BY_TYPE_KEY,
    FAILURE_SWALLOWED_BY_TYPE_TITLE,
    FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY,
    FAILURE_SWALLOWED_SURFACE,
    FAILURE_SWALLOWED_TOTAL_KEY,
    FailureEvidence,
    failure_evidence_from_health,
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


def _records(*logs):
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


def _round_trip(tmp_path, *logs, name="overall_summary.txt"):
    """text → parser → structured health を 1 本で返す。"""

    summary = aggregate_validation_logs_by_function(logs)
    text = format_overall_results_summary(summary)
    path = tmp_path / name
    path.write_text(text + "\n", encoding="utf-8")
    return text, parse_overall_summary_health(path), build_run_health_summary(summary)


def _failure_block(text):
    """`Failure diagnostics:` block だけを取り出す（他 section を混ぜない）。"""

    lines = text.splitlines()
    start = lines.index("  Failure diagnostics:")
    end = start
    while end < len(lines) and lines[end].strip():
        end += 1
    return "\n".join(lines[start:end])


# ---------------------------------------------------------------------------
# evidence contract: 必須 regression 1〜8
# ---------------------------------------------------------------------------


def test_1_complete_observed_zero(tmp_path):
    """observed=2 / missing=0 / 0 件 → `(none)` と exact `0`。"""

    logs = tuple(
        _write_log(
            tmp_path,
            f"f/f_B1_B{index + 2}.log",
            _payload(failures=_producer_swallowed_block(())),
        )
        for index in range(2)
    )
    summary = summarize_failure_diagnostics(_records(*logs))

    assert summary.swallowed_evidence == FailureEvidence(observed=2)
    assert summary.internal_evidence == FailureEvidence(observed=2)
    assert summary.swallowed_evidence.state == EVIDENCE_COMPLETE
    assert summary.swallowed_exact_total == 0
    assert summary.swallowed_observed_total == 0

    text, parsed, built = _round_trip(tmp_path, *logs)
    block = _failure_block(text)
    assert "Swallowed exception evidence: complete (observed 2 / missing 0 / malformed 0)" in block
    assert "Swallowed exceptions total  : 0" in block
    assert f"{FAILURE_SWALLOWED_BY_TYPE_TITLE}:\n      (none)" in block
    assert f"{FAILURE_INTERNAL_BY_SITE_TITLE}:\n      (none)" in block
    assert "(unknown)" not in block
    for health in (parsed, built):
        assert health[FAILURE_SWALLOWED_TOTAL_KEY] == 0
        assert health[FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY] == 0
        assert health[FAILURE_EVIDENCE_KEY][FAILURE_SWALLOWED_SURFACE]["state"] == EVIDENCE_COMPLETE
        assert health[FAILURE_EVIDENCE_KEY][FAILURE_INTERNAL_SURFACE]["state"] == EVIDENCE_COMPLETE
    rendered = format_run_health_summary(built)
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: 0" in rendered
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (none)" in rendered
    assert f"  {FAILURE_INTERNAL_BY_SITE_KEY}:\n    (none)" in rendered


def test_2_all_missing_is_unknown_not_zero(tmp_path):
    """observed=0 / missing>0 → 両 surface `(unknown)`、exact total を主張しない。"""

    logs = (
        _write_log(tmp_path, "f/f_B1_B2.log", _payload()),
        _write_log(tmp_path, "f/f_B1_B3.log", human_result="Result: UNKNOWN"),
    )
    summary = summarize_failure_diagnostics(_records(*logs))

    assert summary.swallowed_evidence == FailureEvidence(missing=2)
    assert summary.swallowed_evidence.state == EVIDENCE_UNKNOWN
    assert summary.internal_evidence.state == EVIDENCE_UNKNOWN
    assert summary.swallowed_exact_total is None

    text, parsed, built = _round_trip(tmp_path, *logs)
    block = _failure_block(text)
    assert "Swallowed exception evidence: unknown (observed 0 / missing 2 / malformed 0)" in block
    assert "Internal exception evidence : unknown (observed 0 / missing 2 / malformed 0)" in block
    assert "Swallowed exceptions total  : unknown (observed 0)" in block
    assert f"{FAILURE_SWALLOWED_BY_TYPE_TITLE}:\n      (unknown)" in block
    assert f"{FAILURE_INTERNAL_BY_SITE_TITLE}:\n      (unknown)" in block
    assert "(none)" not in block
    for health in (parsed, built):
        assert health[FAILURE_SWALLOWED_TOTAL_KEY] is None
        assert health[FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY] == 0
    rendered = format_run_health_summary(built)
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: unknown (observed 0)" in rendered
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (unknown)" in rendered
    assert f"  {FAILURE_INTERNAL_BY_SITE_KEY}:\n    (unknown)" in rendered


def test_3_partial_observed_zero_plus_missing(tmp_path):
    """observed=1（0 件）/ missing=1 → run 全体を `(none)` / exact 0 にしない。"""

    logs = (
        _write_log(
            tmp_path, "f/f_B1_B2.log",
            _payload(failures=_producer_swallowed_block(())),
        ),
        _write_log(tmp_path, "f/f_B1_B3.log", _payload()),
    )
    summary = summarize_failure_diagnostics(_records(*logs))

    assert summary.swallowed_evidence == FailureEvidence(observed=1, missing=1)
    assert summary.swallowed_evidence.state == EVIDENCE_PARTIAL
    assert summary.internal_evidence.state == EVIDENCE_PARTIAL
    assert summary.swallowed_exact_total is None
    assert summary.swallowed_observed_total == 0

    text, parsed, built = _round_trip(tmp_path, *logs)
    block = _failure_block(text)
    assert "Swallowed exception evidence: partial (observed 1 / missing 1 / malformed 0)" in block
    assert "Internal exception evidence : partial (observed 1 / missing 1 / malformed 0)" in block
    assert "Swallowed exceptions total  : unknown (observed 0)" in block
    # 観測できた側が 0 件でも、run 全体では `(none)` と言えない。
    assert f"{FAILURE_SWALLOWED_BY_TYPE_TITLE}:\n      (unknown)" in block
    assert f"{FAILURE_INTERNAL_BY_SITE_TITLE}:\n      (unknown)" in block
    assert "(none)" not in block
    for health in (parsed, built):
        assert health[FAILURE_SWALLOWED_TOTAL_KEY] is None
        assert health[FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY] == 0
        assert health[FAILURE_EVIDENCE_KEY][FAILURE_INTERNAL_SURFACE] == {
            "state": EVIDENCE_PARTIAL, "observed": 1, "missing": 1, "malformed": 0,
        }


def test_4_partial_observed_nonzero_keeps_the_observed_counts(tmp_path):
    """observed 側の `ValueError: 3` は保持しつつ、exact total とは分ける。"""

    logs = (
        _write_log(
            tmp_path, "f/f_B1_B2.log",
            _payload(failures=_producer_swallowed_block(
                ((None, ValueError("v"), "analysis.a", 3),)
            )),
        ),
        _write_log(tmp_path, "f/f_B1_B3.log", _payload()),
    )
    summary = summarize_failure_diagnostics(_records(*logs))

    assert summary.swallowed_evidence.state == EVIDENCE_PARTIAL
    assert summary.swallowed_exact_total is None
    assert summary.swallowed_observed_total == 3
    assert summary.swallowed_exceptions_by_type == {"ValueError": 3}

    text, parsed, built = _round_trip(tmp_path, *logs)
    block = _failure_block(text)
    assert "Swallowed exceptions total  : unknown (observed 3)" in block
    assert f"{FAILURE_SWALLOWED_BY_TYPE_TITLE}:\n      - ValueError: 3" in block
    for health in (parsed, built):
        assert health[FAILURE_SWALLOWED_TOTAL_KEY] is None
        assert health[FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY] == 3
        assert health[FAILURE_SWALLOWED_BY_TYPE_KEY] == {"ValueError": 3}
        assert health[FAILURE_EVIDENCE_KEY][FAILURE_SWALLOWED_SURFACE]["state"] == EVIDENCE_PARTIAL
    rendered = format_run_health_summary(built)
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: unknown (observed 3)" in rendered
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    - ValueError: 3" in rendered
    assert built[FAILURE_SWALLOWED_BY_SITE_KEY] == {"analysis.a": 3}


def test_5_malformed_swallowed_ledger_is_not_an_observed_zero(tmp_path):
    """握り潰し surface が読めない pair を observed-zero にしない。"""

    broken = (
        # by_site が list でない
        {"swallowed_exceptions": {"total": 3, "by_site": "not-a-list"}},
        # 宣言 total と行の合計が食い違う
        {"swallowed_exceptions": {"total": 9, "by_site": []}},
        # `swallowed_exceptions` key そのものが欠落
        {"internal_exception": {"exception_type": "RuntimeError", "site": "checker.checker"}},
    )
    logs = tuple(
        _write_log(tmp_path, f"f/f_B1_B{index + 2}.log", _payload(failures=failures))
        for index, failures in enumerate(broken)
    )
    summary = summarize_failure_diagnostics(_records(*logs))

    assert summary.swallowed_evidence == FailureEvidence(malformed=3)
    assert summary.swallowed_evidence.state == EVIDENCE_UNKNOWN
    assert summary.swallowed_exact_total is None
    assert summary.swallowed_exceptions_by_type == {}
    # 内部エラー surface は 3 pair とも読めているので complete のまま。
    assert summary.internal_evidence == FailureEvidence(observed=3)
    assert summary.internal_exception_by_site == {"checker.checker": 1}

    text, parsed, built = _round_trip(tmp_path, *logs)
    block = _failure_block(text)
    assert "Swallowed exception evidence: unknown (observed 0 / missing 0 / malformed 3)" in block
    assert "Internal exception evidence : complete (observed 3 / missing 0 / malformed 0)" in block
    assert "Swallowed exceptions total  : unknown (observed 0)" in block
    assert f"{FAILURE_SWALLOWED_BY_TYPE_TITLE}:\n      (unknown)" in block
    assert f"{FAILURE_INTERNAL_BY_SITE_TITLE}:\n      - checker.checker: 1" in block
    for health in (parsed, built):
        assert health[FAILURE_SWALLOWED_TOTAL_KEY] is None
        assert health[FAILURE_EVIDENCE_KEY][FAILURE_INTERNAL_SURFACE]["state"] == EVIDENCE_COMPLETE


def test_5a_missing_declared_total_is_malformed_not_an_exact_zero(tmp_path):
    """`total` key 欠落は producer 契約外。`by_site` だけで exact 0 を名乗らない。"""

    failures = {"swallowed_exceptions": {"by_site": []}}
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary = summarize_failure_diagnostics(_records(log))

    assert summary.swallowed_evidence == FailureEvidence(malformed=1)
    assert summary.swallowed_evidence.state == EVIDENCE_UNKNOWN
    assert summary.swallowed_exact_total is None
    assert summary.swallowed_observed_total == 0

    text, parsed, built = _round_trip(tmp_path, log)
    block = _failure_block(text)
    assert "Swallowed exception evidence: unknown (observed 0 / missing 0 / malformed 1)" in block
    assert "Swallowed exceptions total  : unknown (observed 0)" in block
    assert f"{FAILURE_SWALLOWED_BY_TYPE_TITLE}:\n      (unknown)" in block
    assert "(none)" not in block.split(FAILURE_INTERNAL_BY_SITE_TITLE)[0]
    for health in (parsed, built):
        assert health[FAILURE_SWALLOWED_TOTAL_KEY] is None
        assert health[FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY] == 0
        assert health[FAILURE_EVIDENCE_KEY][FAILURE_SWALLOWED_SURFACE]["state"] == EVIDENCE_UNKNOWN
    rendered = format_run_health_summary(built)
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: unknown (observed 0)" in rendered
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: 0" not in rendered


def test_5c_swallowed_ledger_schema_boundaries(tmp_path):
    """producer 契約の各境界。readable なのは契約を全部満たすときだけ。"""

    rows = [{"site": "analysis.a", "exception_type": "ValueError", "count": 2}]
    malformed_ledgers = {
        "total key missing": {"by_site": []},
        "total is None": {"total": None, "by_site": []},
        "total is True": {"total": True, "by_site": [
            {"site": "s", "exception_type": "E", "count": 1}
        ]},
        "total is negative": {"total": -1, "by_site": []},
        "total is a string": {"total": "0", "by_site": []},
        "total is a float": {"total": 0.0, "by_site": []},
        "by_site key missing": {"total": 0},
        "by_site is not a sequence": {"total": 0, "by_site": {}},
        "by_site is a string": {"total": 0, "by_site": ""},
        "row is not a mapping": {"total": 0, "by_site": ["row"]},
        "count key missing": {"total": 0, "by_site": [{"site": "s"}]},
        "count is negative": {"total": -1, "by_site": [{"site": "s", "count": -1}]},
        "count is a bool": {"total": 1, "by_site": [{"site": "s", "count": True}]},
        "declared total mismatch": {"total": 5, "by_site": rows},
    }
    for label, ledger in malformed_ledgers.items():
        log = _write_log(
            tmp_path / label.replace(" ", "_"),
            "f/f_B1_B2.log",
            _payload(failures={"swallowed_exceptions": ledger}),
        )
        summary = summarize_failure_diagnostics(_records(log))
        assert summary.swallowed_evidence.malformed == 1, label
        assert summary.swallowed_evidence.observed == 0, label
        assert summary.swallowed_exact_total is None, label

    valid_ledgers = {
        "observed zero": ({"total": 0, "by_site": []}, 0, {}),
        "observed nonzero": ({"total": 2, "by_site": rows}, 2, {"ValueError": 2}),
    }
    for label, (ledger, expected_total, expected_by_type) in valid_ledgers.items():
        log = _write_log(
            tmp_path / label.replace(" ", "_"),
            "f/f_B1_B2.log",
            _payload(failures={"swallowed_exceptions": ledger}),
        )
        summary = summarize_failure_diagnostics(_records(log))
        assert summary.swallowed_evidence == FailureEvidence(observed=1), label
        assert summary.swallowed_evidence.state == EVIDENCE_COMPLETE, label
        assert summary.swallowed_exact_total == expected_total, label
        assert summary.swallowed_exceptions_by_type == expected_by_type, label


def test_5d_an_empty_failures_block_is_malformed_for_both_surfaces(tmp_path):
    """block はあるが中身が無い payload を「観測して 0 件」にしない。

    `failures` key ごと無い log（PR-125-A 以前）は `missing`、空 block は
    `malformed`。どちらも complete にはならないが、意味が違うので分ける。
    """

    empty = _write_log(tmp_path / "empty", "f/f_B1_B2.log", _payload(failures={}))
    summary = summarize_failure_diagnostics(_records(empty))
    assert summary.swallowed_evidence == FailureEvidence(malformed=1)
    assert summary.internal_evidence == FailureEvidence(malformed=1)
    assert summary.swallowed_exact_total is None

    # `diagnostics` はあるが `failures` key が無い payload は未観測。
    no_key = _write_log(
        tmp_path / "no_key", "f/f_B1_B2.log",
        _payload(diagnostics={"schema": "result-diagnostics-v1", "stages": {}}),
    )
    summary = summarize_failure_diagnostics(_records(no_key))
    assert summary.swallowed_evidence == FailureEvidence(missing=1)
    assert summary.internal_evidence == FailureEvidence(missing=1)


def test_5f_a_broken_failures_value_is_malformed_not_missing(tmp_path):
    """`failures` key が **ある**のに値が壊れている log は未観測ではない。

    * `diagnostics` / `failures` の key が無い旧 log → `missing`
    * `failures=None` / 非 mapping → 両 surface `malformed`

    どちらも exact 0 は名乗らないが、「PR-125-A 以前の log」と
    「PR-125-A 以降だが観測 surface が壊れている」は別の事実なので分ける。
    """

    def _summary(directory, payload):
        return summarize_failure_diagnostics(
            _records(_write_log(tmp_path / directory, "f/f_B1_B2.log", payload))
        )

    # (a) failures key ごと無い → missing
    missing = _summary(
        "no_failures_key",
        _payload(diagnostics={"schema": "result-diagnostics-v1", "stages": {}}),
    )
    assert missing.swallowed_evidence == FailureEvidence(missing=1)
    assert missing.internal_evidence == FailureEvidence(missing=1)

    # (b) failures=None / 非 mapping → malformed
    for label, broken in (
        ("null", None),
        ("string", "broken"),
        ("list", []),
        ("int", 0),
    ):
        summary = _summary(
            f"broken_{label}",
            _payload(diagnostics={"schema": "result-diagnostics-v1", "failures": broken}),
        )
        assert summary.swallowed_evidence == FailureEvidence(malformed=1), label
        assert summary.internal_evidence == FailureEvidence(malformed=1), label
        assert summary.swallowed_exact_total is None, label

    # (c) diagnostics 自体が壊れている場合も未観測ではなく malformed
    broken_diagnostics = _summary("broken_diagnostics", _payload(diagnostics="broken"))
    assert broken_diagnostics.swallowed_evidence == FailureEvidence(malformed=1)
    assert broken_diagnostics.internal_evidence == FailureEvidence(malformed=1)

    # (d) diagnostics key ごと無い（最も古い log）→ missing
    oldest = _summary("no_diagnostics", _payload())
    assert oldest.swallowed_evidence == FailureEvidence(missing=1)


def test_5g_broken_failures_value_round_trips_as_malformed(tmp_path):
    """text → parser → structured health まで malformed として往復する。"""

    log = _write_log(
        tmp_path, "f/f_B1_B2.log",
        _payload(diagnostics={"schema": "result-diagnostics-v1", "failures": None}),
    )
    text, parsed, built = _round_trip(tmp_path, log)
    block = _failure_block(text)

    assert "Swallowed exception evidence: unknown (observed 0 / missing 0 / malformed 1)" in block
    assert "Internal exception evidence : unknown (observed 0 / missing 0 / malformed 1)" in block
    assert "Swallowed exceptions total  : unknown (observed 0)" in block
    assert "(none)" not in block
    for health in (parsed, built):
        assert health[FAILURE_SWALLOWED_TOTAL_KEY] is None
        assert health[FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY] == 0
        for surface in (FAILURE_SWALLOWED_SURFACE, FAILURE_INTERNAL_SURFACE):
            assert health[FAILURE_EVIDENCE_KEY][surface] == {
                "state": EVIDENCE_UNKNOWN, "observed": 0, "missing": 0, "malformed": 1,
            }
    rendered = format_run_health_summary(built)
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (unknown)" in rendered
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: 0" not in rendered
    # 旧 log（missing）とは違う事実として読める。
    old_log = _write_log(tmp_path / "old", "f/f_B1_B2.log", _payload())
    _old_text, _old_parsed, old_built = _round_trip(tmp_path / "old", old_log)
    assert old_built[FAILURE_EVIDENCE_KEY][FAILURE_SWALLOWED_SURFACE]["missing"] == 1
    assert old_built[FAILURE_EVIDENCE_KEY][FAILURE_SWALLOWED_SURFACE]["malformed"] == 0


def test_5e_an_explicit_null_internal_exception_is_malformed(tmp_path):
    """key 欠落（観測済み 0 件）と明示的な `None`（契約外）を混同しない。"""

    absent = _producer_swallowed_block(())
    assert "internal_exception" not in absent
    explicit_null = dict(absent, internal_exception=None)

    absent_log = _write_log(tmp_path / "absent", "f/f_B1_B2.log", _payload(failures=absent))
    null_log = _write_log(tmp_path / "null", "f/f_B1_B2.log", _payload(failures=explicit_null))

    assert summarize_failure_diagnostics(
        _records(absent_log)
    ).internal_evidence == FailureEvidence(observed=1)
    assert summarize_failure_diagnostics(
        _records(null_log)
    ).internal_evidence == FailureEvidence(malformed=1)


def test_5b_partially_read_rows_are_kept_but_not_called_complete(tmp_path):
    """行が 1 つ壊れていても、読めた行は捨てずに下限として残す。"""

    failures = {
        "swallowed_exceptions": {
            "total": 5,
            "by_site": [
                {"site": "analysis.a", "exception_type": "ValueError", "count": 3},
                {"site": "analysis.b", "exception_type": "KeyError", "count": "two"},
            ],
        }
    }
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary = summarize_failure_diagnostics(_records(log))

    assert summary.swallowed_evidence == FailureEvidence(malformed=1)
    assert summary.swallowed_exact_total is None
    assert summary.swallowed_observed_total == 3
    assert summary.swallowed_exceptions_by_type == {"ValueError": 3}


def test_6_malformed_internal_exception_keeps_the_swallowed_surface(tmp_path):
    """内部エラー surface が壊れても握り潰しの観測は残す（逆も同じ）。"""

    failures = _producer_swallowed_block(((None, ValueError("v"), "analysis.a", 2),))
    failures["internal_exception"] = "not-a-mapping"
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary = summarize_failure_diagnostics(_records(log))

    assert summary.internal_evidence == FailureEvidence(malformed=1)
    assert summary.internal_evidence.state == EVIDENCE_UNKNOWN
    assert summary.swallowed_evidence == FailureEvidence(observed=1)
    assert summary.swallowed_exact_total == 2
    assert summary.swallowed_exceptions_by_type == {"ValueError": 2}

    text, parsed, built = _round_trip(tmp_path, log)
    block = _failure_block(text)
    assert "Swallowed exception evidence: complete (observed 1 / missing 0 / malformed 0)" in block
    assert "Internal exception evidence : unknown (observed 0 / missing 0 / malformed 1)" in block
    assert "Swallowed exceptions total  : 2" in block
    assert f"{FAILURE_SWALLOWED_BY_TYPE_TITLE}:\n      - ValueError: 2" in block
    # 内部エラーは読めていないので `(none)` にしない。
    assert f"{FAILURE_INTERNAL_BY_SITE_TITLE}:\n      (unknown)" in block
    for health in (parsed, built):
        assert health[FAILURE_SWALLOWED_TOTAL_KEY] == 2
        assert health[FAILURE_EVIDENCE_KEY][FAILURE_INTERNAL_SURFACE]["state"] == EVIDENCE_UNKNOWN


def test_7_a_pre_pr125b_summary_is_unknown_not_zero(tmp_path):
    """PR-125-B 以前の `overall_summary.txt` / health JSON との後方互換。"""

    path = tmp_path / "overall_summary.txt"
    path.write_text(
        "\n".join(
            [
                "  Overall totals              : TOTAL=  2, EQ=  1, NOT_EQ=  0,"
                " ERROR=  0, UNKNOWN=  1, TIMEOUT=  0, INCOMPLETE=  0",
                "    UNKNOWN by reason:",
                "      - outcome_path_region_completeness_unproven: 1",
                "    Operational UNKNOWN by reason:",
                "      (none)",
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    health = parse_overall_summary_health(path)

    assert health[FAILURE_EVIDENCE_KEY] == {}
    assert health[FAILURE_SWALLOWED_TOTAL_KEY] is None
    assert health[FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY] is None
    assert health[FAILURE_SWALLOWED_BY_TYPE_KEY] == {}
    rendered = format_run_health_summary(health)
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (unknown)" in rendered
    assert f"  {FAILURE_INTERNAL_BY_SITE_KEY}:\n    (unknown)" in rendered
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: unknown" in rendered
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: 0" not in rendered
    # 既存 summary parser 契約は不変（`(none)` は観測済み 0 件のまま）。
    assert health["unknown_by_reason"] == {
        "outcome_path_region_completeness_unproven": 1
    }
    assert health["operational_unknown_by_reason"] == {}
    assert health["evidence_missing_sections"] == []
    # key を 1 つも持たない health（PR-125-B 以前の JSON）も同じ扱い。
    legacy = {"total_results": 2, "final_result_counts": {}, "unknown_units": 1}
    legacy_text = format_run_health_summary(legacy)
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (unknown)" in legacy_text
    assert f"    - {FAILURE_SWALLOWED_SURFACE}: unknown" in legacy_text
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: unknown" in legacy_text


def test_7b_an_incomplete_evidence_row_is_not_restored_as_complete(tmp_path):
    """health mapping 側でも欠けた次元を 0 で埋めない（fail-closed）。"""

    for broken in (
        {"observed": 2},                                            # missing/malformed 欠落
        {"observed": 2, "missing": 0},                              # malformed 欠落
        {"observed": 2, "missing": 0, "malformed": None},           # 非 int
        {"observed": 2, "missing": 0, "malformed": True},           # bool
        {"observed": -1, "missing": 0, "malformed": 0},             # 負数
        # 件数と矛盾する state を書いた health は信用しない。
        {"state": EVIDENCE_COMPLETE, "observed": 1, "missing": 1, "malformed": 0},
    ):
        health = {
            FAILURE_EVIDENCE_KEY: {
                FAILURE_SWALLOWED_SURFACE: broken,
                FAILURE_INTERNAL_SURFACE: broken,
            },
            FAILURE_SWALLOWED_TOTAL_KEY: 0,
            FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY: 0,
        }
        rendered = format_run_health_summary(health)
        assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (unknown)" in rendered, broken
        assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: unknown (observed 0)" in rendered, broken
        assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: 0" not in rendered, broken


def test_7c_evidence_counts_must_account_for_every_pair(tmp_path):
    """`total_results` が分かる health では 3 次元の合計が一致していること。

    合計が pair 総数に届かない evidence からは complete も exact total も
    導けないので、その surface の evidence を信用しない（fail-closed）。
    """

    def _health(total_results, observed, missing, malformed, **extra):
        row = {"observed": observed, "missing": missing, "malformed": malformed}
        health = {
            FAILURE_EVIDENCE_KEY: {
                FAILURE_SWALLOWED_SURFACE: dict(row),
                FAILURE_INTERNAL_SURFACE: dict(row),
            },
            FAILURE_SWALLOWED_TOTAL_KEY: 0,
            FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY: 0,
        }
        if total_results is not None:
            health["total_results"] = total_results
        health.update(extra)
        return health

    # 合計が総数に足りない → reject
    rejected = _health(2, 1, 0, 0)
    assert failure_evidence_from_health(rejected, FAILURE_SWALLOWED_SURFACE) is None
    assert failure_evidence_from_health(rejected, FAILURE_INTERNAL_SURFACE) is None
    rendered = format_run_health_summary(rejected)
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (unknown)" in rendered
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: 0" not in rendered
    assert f"    - {FAILURE_SWALLOWED_SURFACE}: unknown" in rendered

    # 合計が一致 → accept
    accepted = _health(2, 1, 1, 0)
    assert failure_evidence_from_health(
        accepted, FAILURE_SWALLOWED_SURFACE
    ) == FailureEvidence(observed=1, missing=1)
    assert EVIDENCE_PARTIAL in format_run_health_summary(accepted)

    # 合計が総数を超える → reject
    assert failure_evidence_from_health(_health(2, 2, 1, 0), FAILURE_SWALLOWED_SURFACE) is None

    # complete を名乗る evidence も合計が合わなければ reject
    over = _health(3, 2, 0, 0)
    assert failure_evidence_from_health(over, FAILURE_SWALLOWED_SURFACE) is None
    assert f"  {FAILURE_SWALLOWED_TOTAL_KEY}: 0" not in format_run_health_summary(over)

    # `total_results` が不正なら complete を導かない
    for bad_total in (True, -1, "2", 2.0, None):
        health = _health(2, 2, 0, 0)
        health["total_results"] = bad_total
        assert failure_evidence_from_health(health, FAILURE_SWALLOWED_SURFACE) is None, bad_total

    # `total_results` を持たない legacy health は既存どおり（勝手に 0 を推測しない）
    legacy = _health(None, 2, 0, 0)
    assert "total_results" not in legacy
    assert failure_evidence_from_health(
        legacy, FAILURE_SWALLOWED_SURFACE
    ) == FailureEvidence(observed=2)

    # surface ごとに独立して判定する。
    mixed = _health(2, 1, 1, 0)
    mixed[FAILURE_EVIDENCE_KEY][FAILURE_INTERNAL_SURFACE] = {
        "observed": 1, "missing": 0, "malformed": 0,
    }
    assert failure_evidence_from_health(
        mixed, FAILURE_SWALLOWED_SURFACE
    ) == FailureEvidence(observed=1, missing=1)
    assert failure_evidence_from_health(mixed, FAILURE_INTERNAL_SURFACE) is None


def test_7d_real_summaries_keep_evidence_consistent_with_total_results(tmp_path):
    """自分が書いた summary / health は常にこの不変量を満たす。"""

    logs = (
        _write_log(
            tmp_path, "f/f_B1_B2.log",
            _payload(failures=_producer_swallowed_block(())),
        ),
        _write_log(tmp_path, "f/f_B1_B3.log", _payload()),
        _write_log(
            tmp_path, "f/f_B1_B4.log",
            _payload(diagnostics={"schema": "result-diagnostics-v1", "failures": None}),
        ),
    )
    _text, parsed, built = _round_trip(tmp_path, *logs)

    for health in (parsed, built):
        assert health["total_results"] == 3
        for surface in (FAILURE_SWALLOWED_SURFACE, FAILURE_INTERNAL_SURFACE):
            evidence = failure_evidence_from_health(health, surface)
            assert evidence is not None, surface
            assert evidence.observed + evidence.missing + evidence.malformed == 3
            assert evidence == FailureEvidence(observed=1, missing=1, malformed=1)


def test_8_mixed_old_and_new_logs_are_partial(tmp_path):
    """新旧 log が混ざった run は partial。内部エラーも `(none)` にしない。"""

    failures = _producer_swallowed_block(((None, OSError("io"), "ghidra.broker", 2),))
    logs = (
        _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures)),
        _write_log(tmp_path, "f/f_B1_B3.log", _payload()),
    )
    summary = summarize_failure_diagnostics(_records(*logs))

    assert summary.swallowed_evidence == FailureEvidence(observed=1, missing=1)
    assert summary.internal_evidence == FailureEvidence(observed=1, missing=1)
    assert summary.swallowed_exact_total is None
    assert summary.swallowed_observed_total == 2
    assert summary.swallowed_exceptions_by_type == {"OSError": 2}

    block = _failure_block(_round_trip(tmp_path, *logs)[0])
    assert f"{FAILURE_INTERNAL_BY_SITE_TITLE}:\n      (unknown)" in block
    assert "(none)" not in block


# ---------------------------------------------------------------------------
# 集計そのもの
# ---------------------------------------------------------------------------


def test_swallowed_exceptions_are_counted_by_type_and_by_site(tmp_path):
    failures = _producer_swallowed_block((
        ("return_width_bridge_missing", ValueError("a"), "analysis.returns.widths", 2),
        (None, KeyError("b"), "analysis.returns.widths", 1),
        (None, ValueError("c"), "semantics.normalize.fold", 3),
    ))
    assert failures[FAILURE_SWALLOWED_EXCEPTIONS]["total"] == 6

    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary = summarize_failure_diagnostics(_records(log))

    assert summary.swallowed_exact_total == 6
    assert summary.swallowed_exceptions_by_type == {"KeyError": 1, "ValueError": 5}
    assert summary.swallowed_exceptions_by_site == {
        "analysis.returns.widths": 3,
        "semantics.normalize.fold": 3,
    }
    assert summary.internal_exception_by_site == {}
    assert summary.swallowed_evidence == FailureEvidence(observed=1)


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
    summary = summarize_failure_diagnostics(_records(*logs))

    assert summary.internal_exception_by_site == {
        "analysis.returns.analyze_function": 1,
        "checker.checker.EquivalenceChecker.check": 2,
    }
    assert summary.swallowed_exceptions_by_type == {"ValueError": 1}
    assert summary.internal_evidence == FailureEvidence(observed=3)


def test_multiple_pairs_add_up(tmp_path):
    logs = []
    for index in range(4):
        failures = _producer_swallowed_block(
            ((None, TypeError("t"), f"analysis.site{index % 2}", index + 1),)
        )
        logs.append(
            _write_log(tmp_path, f"f/f_B1_B{index + 2}.log", _payload(failures=failures))
        )
    summary = summarize_failure_diagnostics(_records(*logs))

    assert summary.swallowed_exact_total == 1 + 2 + 3 + 4
    assert summary.swallowed_exceptions_by_type == {"TypeError": 10}
    assert summary.swallowed_exceptions_by_site == {
        "analysis.site0": 1 + 3,
        "analysis.site1": 2 + 4,
    }


def test_only_the_final_payload_of_a_pair_is_counted(tmp_path):
    early = _producer_swallowed_block(((None, ValueError("early"), "analysis.a", 5),))
    final = _producer_swallowed_block(((None, ValueError("final"), "analysis.a", 1),))
    log = _write_log(
        tmp_path, "f/f_B1_B2.log", _payload(failures=early), _payload(failures=final)
    )
    summary = summarize_failure_diagnostics(_records(log))

    assert summary.swallowed_evidence == FailureEvidence(observed=1)
    assert summary.swallowed_exact_total == 1


def test_missing_site_or_type_uses_the_existing_missing_marker(tmp_path):
    failures = {
        "swallowed_exceptions": {
            "total": 2,
            "by_site": [{"site": None, "exception_type": None, "count": 2}],
        },
        "internal_exception": {"exception_type": "RuntimeError", "stack": []},
    }
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary = summarize_failure_diagnostics(_records(log))

    assert summary.swallowed_exceptions_by_type == {"<missing>": 2}
    assert summary.swallowed_exceptions_by_site == {"<missing>": 2}
    assert summary.internal_exception_by_site == {"<missing>": 1}
    assert summary.swallowed_evidence == FailureEvidence(observed=1)
    assert summary.internal_evidence == FailureEvidence(observed=1)


def test_empty_run_is_complete_with_zero_pairs(tmp_path):
    summary = summarize_failure_diagnostics(())

    assert summary.swallowed_evidence == FailureEvidence()
    assert summary.swallowed_evidence.state == EVIDENCE_COMPLETE
    assert summary.swallowed_exact_total == 0
    text = format_failure_diagnostics_summary(summary)
    assert "Swallowed exceptions total  : 0" in text
    assert f"{FAILURE_SWALLOWED_BY_TYPE_TITLE}:\n    (none)" in text


# ---------------------------------------------------------------------------
# summary surface と parser
# ---------------------------------------------------------------------------


def test_overall_summary_carries_both_new_sections(tmp_path):
    failures = _producer_swallowed_block((
        (None, ValueError("v"), "analysis.a", 2),
        (None, KeyError("k"), "analysis.b", 1),
    ))
    failures.update(
        _producer_internal_block("checker.checker.EquivalenceChecker.check", OSError("x"))
    )
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    text, _parsed, _built = _round_trip(tmp_path, log)

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
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    _text, parsed, built = _round_trip(tmp_path, log)

    assert parsed[FAILURE_SWALLOWED_BY_TYPE_KEY] == {"ValueError": 2, "KeyError": 1}
    assert parsed[FAILURE_INTERNAL_BY_SITE_KEY] == {"proof.strategies.pairwise": 1}
    assert parsed[FAILURE_EVIDENCE_KEY] == {
        FAILURE_SWALLOWED_SURFACE: {
            "state": EVIDENCE_COMPLETE, "observed": 1, "missing": 0, "malformed": 0,
        },
        FAILURE_INTERNAL_SURFACE: {
            "state": EVIDENCE_COMPLETE, "observed": 1, "missing": 0, "malformed": 0,
        },
    }
    assert parsed[FAILURE_SWALLOWED_TOTAL_KEY] == 3
    # structured summary は site 別の握り潰しも保持する（text には出さない次元）。
    assert built[FAILURE_SWALLOWED_BY_SITE_KEY] == {"analysis.a": 2, "analysis.b": 1}
    for key in (
        FAILURE_SWALLOWED_BY_TYPE_KEY,
        FAILURE_INTERNAL_BY_SITE_KEY,
        FAILURE_EVIDENCE_KEY,
        FAILURE_SWALLOWED_TOTAL_KEY,
        FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY,
    ):
        assert built[key] == parsed[key]


def test_new_sections_do_not_swallow_the_following_section(tmp_path):
    """新節の直後に来る既存 section の行を吸い込まないこと。"""

    path = tmp_path / "overall_summary.txt"
    path.write_text(
        "\n".join(
            [
                "  Overall totals              : TOTAL=  3, EQ=  1, NOT_EQ=  0,"
                " ERROR=  0, UNKNOWN=  2, TIMEOUT=  0, INCOMPLETE=  0",
                "  Failure diagnostics:",
                "    Swallowed exception evidence: partial (observed 2 / missing 1 / malformed 0)",
                "    Internal exception evidence : complete (observed 3 / missing 0 / malformed 0)",
                "    Swallowed exceptions total  : unknown (observed 3)",
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
    assert health[FAILURE_SWALLOWED_TOTAL_KEY] is None
    assert health[FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY] == 3
    assert health[FAILURE_EVIDENCE_KEY][FAILURE_SWALLOWED_SURFACE]["state"] == EVIDENCE_PARTIAL
    assert health[FAILURE_EVIDENCE_KEY][FAILURE_INTERNAL_SURFACE]["state"] == EVIDENCE_COMPLETE
    assert health["operational_unknown_by_reason"] == {
        "expression_semantics_unsupported": 7
    }
    assert health["unknown_by_reason"] == {
        "outcome_path_region_completeness_unproven": 9
    }
    assert health["total_results"] == 3
    # 3 次元の合計は pair 総数と一致する（fixture も不変量を満たす）。
    for surface in (FAILURE_SWALLOWED_SURFACE, FAILURE_INTERNAL_SURFACE):
        assert failure_evidence_from_health(health, surface) is not None
    # `(none)` marker は既存契約どおり `evidence_missing_sections` に入らない。
    assert FAILURE_INTERNAL_BY_SITE_KEY not in health["evidence_missing_sections"]


def test_unknown_marker_round_trips_for_the_new_sections(tmp_path):
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload())
    _text, health, _built = _round_trip(tmp_path, log)

    assert FAILURE_SWALLOWED_BY_TYPE_KEY in health["evidence_missing_sections"]
    assert FAILURE_INTERNAL_BY_SITE_KEY in health["evidence_missing_sections"]
    rendered = format_run_health_summary(health)
    assert f"  {FAILURE_SWALLOWED_BY_TYPE_KEY}:\n    (unknown)" in rendered
    assert f"  {FAILURE_INTERNAL_BY_SITE_KEY}:\n    (unknown)" in rendered


def test_existing_summary_sections_are_unchanged_by_the_new_block(tmp_path):
    """新 block を取り除くと PR-128-A 時点の出力と 1 文字も変わらないこと。"""

    failures = _producer_swallowed_block(((None, ValueError("v"), "analysis.a", 1),))
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    summary = aggregate_validation_logs_by_function((log,))
    text = format_overall_results_summary(summary)
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


def test_health_summary_json_keeps_the_planned_dimensions(tmp_path):
    failures = _producer_swallowed_block(((None, ValueError("v"), "analysis.a", 4),))
    failures.update(_producer_internal_block("smt.parallel.run_single", OSError("x")))
    log = _write_log(tmp_path, "f/f_B1_B2.log", _payload(failures=failures))
    health = build_run_health_summary(aggregate_validation_logs_by_function((log,)))

    assert health[FAILURE_SWALLOWED_BY_TYPE_KEY] == {"ValueError": 4}
    assert health[FAILURE_SWALLOWED_BY_SITE_KEY] == {"analysis.a": 4}
    assert health[FAILURE_INTERNAL_BY_SITE_KEY] == {"smt.parallel.run_single": 1}
    assert health[FAILURE_SWALLOWED_TOTAL_KEY] == 4
    assert health[FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY] == 4
    # JSON 化しても壊れない（exact total は None になり得るので null 許容）。
    assert json.loads(json.dumps(health))[FAILURE_SWALLOWED_TOTAL_KEY] == 4
    # 既存 key を落としていない。
    for key in (
        "unknown_by_reason",
        "proof_backlog_by_reason",
        "operational_unknown_by_reason",
        "error_kind_counts",
        "final_result_counts",
    ):
        assert key in health


def test_exact_total_is_null_in_json_when_evidence_is_incomplete(tmp_path):
    logs = (
        _write_log(
            tmp_path, "f/f_B1_B2.log",
            _payload(failures=_producer_swallowed_block(
                ((None, ValueError("v"), "analysis.a", 3),)
            )),
        ),
        _write_log(tmp_path, "f/f_B1_B3.log", _payload()),
    )
    health = build_run_health_summary(aggregate_validation_logs_by_function(logs))
    round_tripped = json.loads(json.dumps(health))

    assert round_tripped[FAILURE_SWALLOWED_TOTAL_KEY] is None
    assert round_tripped[FAILURE_SWALLOWED_OBSERVED_TOTAL_KEY] == 3
