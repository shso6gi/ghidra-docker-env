# -*- coding: utf-8 -*-
"""Issue #125 PR-125-A: typed analysis failures の型・配管・診断・消費側。

帰属契約は `test_issue125_limitation_attribution.py`、最終化までの E2E は
`test_issue125_limitation_finalization.py`。ここは

* `core/errors.py` の型と dependency rule
* 新 domain の sealed registry が 1 reason だけであること
* catch-all の分類と `diagnostics["failures"]`
* 握り潰し台帳の thread safety / reset
* `LegacyBoundaryErrorKind` の 3 member と写像
* 新 3 status が ERROR 再実行対象に入ること
* 診断が `authority` / `proof` の判定入力に読まれないこと
* producer-sites manifest の delta が **ちょうど +1 site**

を固定する。
"""

import ast
import inspect
import json
import threading
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import pytest

from scripts.function_tracer_pcode.core import errors as core_errors
from scripts.function_tracer_pcode.core.errors import (
    AnalysisFailureError,
    AnalysisLimitation,
    CauseAttributionKey,
    DeadlineExceeded,
    InternalError,
    log_swallowed,
    reset_swallowed_exceptions,
    swallowed_exception_snapshot,
    swallowed_exception_total,
)


REPO_ROOT = Path(__file__).resolve().parents[4]
PACKAGE_ROOT = REPO_ROOT / "scripts/function_tracer_pcode"


# --- 型と dependency rule -----------------------------------------------------

def test_core_errors_types_and_dependency_rule():
    assert issubclass(AnalysisLimitation, AnalysisFailureError)
    assert issubclass(InternalError, AnalysisFailureError)
    assert issubclass(DeadlineExceeded, AnalysisLimitation)
    assert DeadlineExceeded.REASON_ID == "analysis_budget_exceeded"
    assert issubclass(AnalysisFailureError, Exception)

    source = Path(core_errors.__file__).read_text(encoding="utf-8")
    tree = ast.parse(source)
    imported = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            if node.level:
                raise AssertionError("core/errors.py must not use relative imports")
            imported.add(node.module or "")
    # 標準ライブラリは可、パッケージ内（上位層含む）は不可。
    # `contextlib` / `enum` は Issue #106 PR-106-0 の pair 実行制御
    # （`pair_failure_scope` / `PairStopState`）が使う標準ライブラリ。
    assert imported == {
        "__future__", "contextlib", "dataclasses", "enum", "hashlib",
        "threading", "traceback", "typing",
    }
    assert not any(name.startswith("scripts.") for name in imported)


def test_internal_error_keeps_the_original_cause_and_a_bounded_stack():
    original = RuntimeError("boom")
    try:
        raise original
    except RuntimeError as exc:
        wrapped = InternalError(exc, site="analysis.tracer.trace")

    assert wrapped.__cause__ is original
    assert wrapped.exception_type == "RuntimeError"
    assert wrapped.site == "analysis.tracer.trace"
    assert str(wrapped) == "RuntimeError: boom"
    assert 0 < len(wrapped.stack_lines()) <= core_errors.STACK_LINE_LIMIT
    assert len(wrapped.stack_digest()) == 64
    assert wrapped.stack_digest() == wrapped.stack_digest()


def test_internal_error_requires_an_exception_and_a_site():
    with pytest.raises(TypeError):
        InternalError("not an exception", site="x")
    with pytest.raises(ValueError):
        InternalError(RuntimeError("x"), site="")


def test_analysis_limitation_requires_reason_and_site():
    with pytest.raises(ValueError):
        AnalysisLimitation("", "detail", site="x")
    with pytest.raises(ValueError):
        AnalysisLimitation("r", "detail", site="")
    with pytest.raises(TypeError):
        AnalysisLimitation("r", "detail", site="x", attribution={"reason_id": "r"})


def test_analysis_limitation_defaults_keep_a_non_empty_missing_fact():
    limitation = AnalysisLimitation("r", "detail", site="s")
    assert limitation.missing_semantic_fact == ("analysis_limitation_unresolved", "r")
    assert limitation.target_key == ()
    assert limitation.evidence_refs == ()


# --- 新 domain の sealed registry ---------------------------------------------

def test_analysis_limitation_registry_is_sealed_and_single():
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_LIMITATION_DOMAIN,
        ANALYSIS_LIMITATION_REASON_REGISTRY,
        ANALYSIS_LIMITATION_RECOVERY_REGISTRY,
    )
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
    )

    definitions = ANALYSIS_LIMITATION_REASON_REGISTRY.snapshot()
    assert len(definitions) == 1
    definition = definitions[0]
    assert definition.reason_id == "analysis_budget_exceeded"
    assert definition.domain == ANALYSIS_LIMITATION_DOMAIN
    assert definition.decision_effect == "blocks_decision"
    assert definition.allowed_target_kinds == frozenset({"analysis_limitation"})
    assert definition.allowed_proof_kinds == frozenset({"analysis_budget_proof"})
    assert len(ANALYSIS_LIMITATION_RECOVERY_REGISTRY.snapshot()) == 1

    # 既存の sealed registry と重複しない（`SealedReasonRegistry.build` が拒否する）。
    durable = PROCESS_DURABLE_REASON_REGISTRY.snapshot()
    assert sum(
        1 for item in durable if item.reason_id == "analysis_budget_exceeded"
    ) == 1
    assert sum(
        1 for item in durable if item.domain == ANALYSIS_LIMITATION_DOMAIN
    ) == 1


def test_analysis_limitation_domain_is_the_only_new_producer_route():
    from scripts.function_tracer_pcode.authority.domains import analysis_limitation

    source = Path(analysis_limitation.__file__).read_text(encoding="utf-8")
    tree = ast.parse(source)
    emits = [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and getattr(node.func, "id", "") == "emit_analysis_limitation_signal"
    ]
    assert len(emits) == 1


def test_limitation_signal_rejects_a_foreign_reason():
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        AnalysisLimitationBlockerSignal,
    )

    with pytest.raises(ValueError):
        AnalysisLimitationBlockerSignal(
            declared_reason_id="counterexample_replay_unproven",
            limitation_site="s",
            canonical_target_key=(),
            missing_semantic_fact=(),
        )


# --- catch-all の分類 ---------------------------------------------------------

def _checker():
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

    return EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)


def _mock_analysis():
    from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

    return create_mock_analysis("f", [])


def test_internal_error_becomes_error_internal_exception_with_stack():
    from scripts.function_tracer_pcode.checker import checker as checker_module

    analysis = _mock_analysis()
    checker = _checker()
    try:
        raise ValueError("inner")
    except ValueError as exc:
        typed = InternalError(exc, site="analysis.returns.analyze_function")
    with patch.object(
        checker_module, "assemble_equivalence_result", side_effect=typed,
    ):
        result = checker.check(analysis, analysis, "L", "R")

    assert result.is_equivalent is None
    assert result.failure_status == "internal_exception"
    failure = result.diagnostics["failures"]["internal_exception"]
    assert failure["exception_type"] == "ValueError"
    assert failure["site"] == "analysis.returns.analyze_function"
    assert failure["stack"] and len(failure["stack"]) <= 64
    assert len(failure["stack_digest"]) == 64


def test_generic_exception_error_kind_is_internal_exception():
    """regression: 旧 `legacy_compatibility_error` に戻していないこと。"""
    from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
        LegacyBoundaryErrorKind,
        _issue_legacy_boundary_error,
    )
    from scripts.function_tracer_pcode.checker import checker as checker_module

    analysis = _mock_analysis()
    checker = _checker()
    with patch.object(
        checker_module, "assemble_equivalence_result",
        side_effect=RuntimeError("generic"),
    ):
        result = checker.check(analysis, analysis)

    assert result.failure_status == "internal_exception"
    session = SimpleNamespace(identity=SimpleNamespace(
        result_occurrence_id="result-issue125",
        source_snapshot_fingerprint="snapshot-issue125",
    ))
    artifact = _issue_legacy_boundary_error(session, result)
    assert artifact.error_kind is LegacyBoundaryErrorKind.INTERNAL_EXCEPTION
    assert artifact.error_kind.value == "internal_exception"


def test_legacy_boundary_error_kind_maps_three_new_statuses():
    from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
        LegacyBoundaryErrorKind,
        _issue_legacy_boundary_error,
    )

    # 既存 5 member の値は変えない。
    assert {kind.value for kind in LegacyBoundaryErrorKind} == {
        "function_lookup_miss",
        "strategy_exception",
        "unexpected_pairwise_state",
        "legacy_compatibility_error",
        "return_abi_authority_invalid",
        "internal_exception",
        "unregistered_reason",
        "limitation_unattributed",
    }
    session = SimpleNamespace(identity=SimpleNamespace(
        result_occurrence_id="result-issue125",
        source_snapshot_fingerprint="snapshot-issue125",
    ))
    for status, expected in (
        ("internal_exception", LegacyBoundaryErrorKind.INTERNAL_EXCEPTION),
        ("unregistered_reason", LegacyBoundaryErrorKind.UNREGISTERED_REASON),
        ("limitation_unattributed", LegacyBoundaryErrorKind.LIMITATION_UNATTRIBUTED),
        # 既存の写像は不変
        ("strategy_exception", LegacyBoundaryErrorKind.STRATEGY_EXCEPTION),
        ("something_else", LegacyBoundaryErrorKind.COMPATIBILITY_ERROR),
    ):
        result = SimpleNamespace(
            failure_status=status, error_message="e", failure_message="m",
        )
        assert _issue_legacy_boundary_error(session, result).error_kind is expected


# --- 握り潰し台帳 -------------------------------------------------------------

def test_swallowed_ledger_threadsafe_and_resettable():
    reset_swallowed_exceptions()
    try:
        assert swallowed_exception_snapshot() == []
        assert swallowed_exception_total() == 0

        errors = []

        def worker(index):
            try:
                for _ in range(200):
                    log_swallowed(
                        "reason_a" if index % 2 else None,
                        ValueError("x"),
                        f"site.{index % 3}",
                    )
            except Exception as exc:  # 台帳は診断なので落ちてはいけない
                errors.append(exc)

        threads = [threading.Thread(target=worker, args=(i,)) for i in range(8)]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join()

        assert errors == []
        assert swallowed_exception_total() == 8 * 200
        rows = swallowed_exception_snapshot()
        # `reason_id` は None を取り得るが、順序付けは落ちない。
        assert rows == sorted(
            rows,
            key=lambda row: (
                row["site"], row["exception_type"], row["reason_id"] or "",
            ),
        )
        assert {row["site"] for row in rows} == {"site.0", "site.1", "site.2"}
        assert {row["reason_id"] for row in rows} == {None, "reason_a"}
        # snapshot は集計を消さない。
        assert swallowed_exception_snapshot() == rows

        reset_swallowed_exceptions()
        assert swallowed_exception_snapshot() == []
        assert swallowed_exception_total() == 0
    finally:
        reset_swallowed_exceptions()


def test_log_swallowed_never_raises():
    reset_swallowed_exceptions()
    try:
        class _Hostile(Exception):
            def __str__(self):
                raise RuntimeError("hostile")

        log_swallowed("r", _Hostile(), "site.x")
        assert swallowed_exception_total() == 1
    finally:
        reset_swallowed_exceptions()


# --- diagnostics ---------------------------------------------------------------

def test_attach_failure_diagnostics_merges_and_never_overwrites():
    from scripts.function_tracer_pcode.checker.diagnostics import (
        attach_failure_diagnostics,
        record_failure_diagnostic,
    )

    reset_swallowed_exceptions()
    try:
        log_swallowed(None, ValueError("x"), "analysis.tracer.trace")
        result = SimpleNamespace(diagnostics={
            "stages": {"regions": {}},
            "phases": [{"phase": "P0_BASE"}],
            "boundary_seconds": {"finish": 1.0},
        })
        record_failure_diagnostic(result, "internal_exception", {"site": "s"})
        attach_failure_diagnostics(result)

        # PR-124-A / PR-128-A の診断は残っている。
        assert result.diagnostics["stages"] == {"regions": {}}
        assert result.diagnostics["phases"] == [{"phase": "P0_BASE"}]
        assert result.diagnostics["boundary_seconds"] == {"finish": 1.0}
        failures = result.diagnostics["failures"]
        assert failures["internal_exception"] == {"site": "s"}
        assert failures["swallowed_exceptions"]["total"] == 1
        assert failures["swallowed_exceptions"]["by_site"][0]["site"] == (
            "analysis.tracer.trace"
        )
    finally:
        reset_swallowed_exceptions()


def test_attach_failure_diagnostics_is_fail_open():
    from scripts.function_tracer_pcode.checker.diagnostics import (
        attach_failure_diagnostics,
    )

    class _NoDiagnostics:
        __slots__ = ()

    # 属性を持てない object でも例外にしない。
    attach_failure_diagnostics(_NoDiagnostics())
    attach_failure_diagnostics(None)


def test_result_diagnostics_payload_lists_failures():
    from scripts.function_tracer_pcode.checker.diagnostics import (
        result_diagnostics_payload,
    )
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    result = EquivalenceResult(
        is_equivalent=None, function1_name="l", function2_name="r",
        binary1_name="L", binary2_name="R", solver_results=None,
    )
    result.diagnostics = {"failures": {"internal_exception": {"site": "s"}}}
    payload = result_diagnostics_payload(result)
    assert payload["failures"] == {"internal_exception": {"site": "s"}}
    assert result.to_dict()["diagnostics"]["failures"] == {
        "internal_exception": {"site": "s"}
    }


def test_cli_attaches_failure_diagnostics_before_the_aggregate():
    from scripts.function_tracer_pcode.cli.commands import equivalence

    source = inspect.getsource(equivalence.run_equivalence_check)
    order = [
        source.index("    reset_swallowed_exceptions()\n"),
        # Issue #106 PR-106-0: pair 台帳の reset も同じ「ペア冒頭」区画に置く。
        source.index("    reset_pair_failure_scopes()\n"),
        source.index("stage_clock = StageClock()"),
        source.index("attach_stage_timing(result, stage_clock)"),
        source.index("attach_failure_diagnostics(result)"),
        source.index("attach_cause_aggregate(result)"),
        source.index("result.to_string("),
        source.index("result_payload = result.to_dict()"),
        source.index("build_canonical_result_finalization_bundle("),
    ]
    assert order == sorted(order)


# --- 診断が判定へ漏れない -------------------------------------------------------

def test_failures_not_read_by_authority_or_proof():
    """`authority` / `proof` が診断 block を decision input として読まないこと。

    `checker/diagnostics.py` は `attach_failure_diagnostics` の所有者なので対象外。
    """
    forbidden = ('"failures"', "'failures'", "swallowed_exception", "log_swallowed")
    offenders = []
    for layer in ("authority", "proof"):
        for path in sorted((PACKAGE_ROOT / layer).rglob("*.py")):
            text = path.read_text(encoding="utf-8")
            for needle in forbidden:
                if needle in text:
                    offenders.append((path.relative_to(REPO_ROOT).as_posix(), needle))
    assert offenders == []


def test_semantic_projection_does_not_read_diagnostics():
    from scripts.function_tracer_pcode.authority.decision import canonical_result

    source = inspect.getsource(canonical_result._semantic_projection)
    assert "diagnostics" not in source
    assert "failures" not in source


# --- 消費側（ERROR 再実行） -----------------------------------------------------

@pytest.mark.parametrize("status", [
    "internal_exception", "unregistered_reason", "limitation_unattributed",
])
def test_error_rerun_manifest_includes_three_new_statuses(tmp_path, status):
    import sys

    sys.path.insert(0, str(REPO_ROOT / "scripts/eqbench"))
    try:
        import error_rerun_manifest as erm
    finally:
        sys.path.pop(0)
    from scripts.function_tracer_pcode.reporting.result_summary import (
        classify_log_text,
    )

    payload = {
        "function1_name": "f", "function2_name": "f",
        "binary1_name": "B1", "binary2_name": "B2",
        "is_equivalent": None,
        "error_message": status,
        "failure_status": status,
        "canonical_decision": {
            "schema": "canonical-decision-v1",
            "outcome": "ERROR",
            "error_kind": status,
        },
    }
    text = "\n".join((
        "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
        json.dumps(payload),
        "=== EQUIVALENCE_RESULT_JSON_END ===",
    ))
    assert classify_log_text(text, matrix_context=True) == "ERROR"

    root = tmp_path / "EqBench"
    sample = root / "REVE" / "sample" / "f"
    sample.mkdir(parents=True)
    (sample / "f_B1_B2.log").write_text(text, encoding="utf-8")
    targets = erm.collect(root, "EQ")
    assert len(targets) == 1


# --- producer-sites manifest ----------------------------------------------------

#: PR-125-A の base（`main` `6d64b83`）が持っていた producer site 数。
#: PR-125-A が足してよいのは `analysis-limitation-observed` の 1 件だけ。
PRODUCER_SITE_COUNT_BEFORE_ISSUE125 = 30
NEW_PRODUCER_SITE_ID = "analysis-limitation-observed"

#: PR-125-A の後に別 Issue が足した producer site。site を足す PR は
#: **ここへ 1 行足す**（それ以外の増減はこの test が落とす）。
PRODUCER_SITES_ADDED_AFTER_ISSUE125 = (
    # Issue #15 PR-15-A: 同一バイナリ・同一関数の identity proof。
    "checker-identical-function-identity",
)

#: 現在期待される producer site 総数。
EXPECTED_PRODUCER_SITE_COUNT = (
    PRODUCER_SITE_COUNT_BEFORE_ISSUE125 + 1
    + len(PRODUCER_SITES_ADDED_AFTER_ISSUE125)
)


def _site_contract(payload):
    return {
        row["producer_site_manifest_id"]: {
            "allowed_dispositions": row["allowed_dispositions"],
            "allowed_producer_ids": row["allowed_producer_ids"],
            "domain": row["domain"],
            "expected_cause_slots": row["expected_cause_slots"],
            "emitter": row["emitter"],
        }
        for row in payload["sites"]
    }


def test_producer_sites_manifest_delta_is_exactly_one_site():
    """base からの delta が **ちょうど +1 site** であることを固定する。

    `origin/main` が無い環境（CI の shallow checkout）でも skip せず、件数と
    新 site の一意性で同じ契約を検査する。
    """
    from scripts.function_tracer_pcode.reporting.phase7_producer_manifest import (
        build_phase7_producer_manifest,
        validate_phase7_producer_manifest,
    )

    manifest_path = (
        REPO_ROOT / "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )
    tracked = json.loads(manifest_path.read_text(encoding="utf-8"))
    # 追跡中の manifest は現 HEAD の source と一致している。
    validate_phase7_producer_manifest(REPO_ROOT, tracked)

    built = build_phase7_producer_manifest(REPO_ROOT)
    ids = [row["producer_site_manifest_id"] for row in built["sites"]]
    assert len(ids) == len(set(ids))
    assert built["site_count"] == EXPECTED_PRODUCER_SITE_COUNT
    assert ids.count(NEW_PRODUCER_SITE_ID) == 1
    for site_id in PRODUCER_SITES_ADDED_AFTER_ISSUE125:
        assert ids.count(site_id) == 1
    # 新 domain の site はこの 1 件だけ（2 件目を足したらここで落ちる）。
    assert [
        row["producer_site_manifest_id"] for row in built["sites"]
        if row["domain"] == "analysis_limitation"
    ] == [NEW_PRODUCER_SITE_ID]


def test_producer_sites_manifest_keeps_every_existing_site_contract():
    """既存 site の disposition / producer / cause slot / emitter を変えていない。

    `origin/main` を読めるときだけ実行する上乗せ検査（件数の固定は上の test）。

    PR-125-A が merge されると `origin/main` 側にも新 site が入るので、
    「ちょうど +1」は merge 前しか成り立たない。merge 後も意味が残るように、
    **site を消していないこと**・**追加は新 site 以外に無いこと**・
    **総数が base + 1 のままであること**で固定する。
    """
    import subprocess

    from scripts.function_tracer_pcode.reporting.phase7_producer_manifest import (
        build_phase7_producer_manifest,
    )

    base = subprocess.run(
        ["git", "show", "origin/main:artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"],
        cwd=REPO_ROOT, capture_output=True, text=True,
    )
    if base.returncode != 0:
        pytest.skip("origin/main producer manifest is unavailable")
    before = json.loads(base.stdout)
    after = json.loads(json.dumps(
        build_phase7_producer_manifest(REPO_ROOT), sort_keys=True
    ))

    before_ids = {row["producer_site_manifest_id"] for row in before["sites"]}
    after_ids = {row["producer_site_manifest_id"] for row in after["sites"]}
    # merge 前は {NEW_PRODUCER_SITE_ID}、merge 後は空集合。どちらでも
    # 「宣言した site 以外は増えていない」ことは変わらない。
    assert after_ids - before_ids <= {
        NEW_PRODUCER_SITE_ID, *PRODUCER_SITES_ADDED_AFTER_ISSUE125
    }
    assert before_ids - after_ids == set()
    assert len(after_ids) == EXPECTED_PRODUCER_SITE_COUNT

    before_contract = _site_contract(before)
    after_contract = _site_contract(after)
    for site_id, contract in before_contract.items():
        assert after_contract[site_id] == contract, site_id


def test_new_producer_site_is_reachable_from_the_sealed_spec():
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_LIMITATION_OBSERVED_SITE,
    )
    from scripts.function_tracer_pcode.reporting.phase7_producer_manifest import (
        build_phase7_producer_manifest,
    )

    rows = {
        row["producer_site_manifest_id"]: row
        for row in build_phase7_producer_manifest(REPO_ROOT)["sites"]
    }
    row = rows[ANALYSIS_LIMITATION_OBSERVED_SITE.site_id]
    assert row["allowed_dispositions"] == ("ELIGIBLE",)
    assert row["allowed_producer_ids"] == ("analysis-limitation-producer-v1",)
    assert row["enclosing_function"] == "observe_analysis_limitation"
    assert [slot["allowed_reason_ids"] for slot in row["expected_cause_slots"]] == [
        ("analysis_budget_exceeded",)
    ]
    assert row["expected_cause_slots"][0]["expected_identity_scope"] == "RELATIONAL"


def test_pilot_accepts_the_new_sealed_reason():
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        PILOT_TYPED_CAUSE_KINDS,
    )

    assert "analysis_budget_exceeded" in PILOT_TYPED_CAUSE_KINDS


def test_attribution_key_is_the_exact_cause_identity_input():
    """帰属キーの field は `CauseIdV2.create()` の入力 + target_kind + requirement。

    `semantic_proposition` だけでは `semantic_proposition_digest` を再現できない
    ので、proposition を構成する 3 入力も持つ（持たないと照合を省略することになる）。
    """
    from dataclasses import fields

    from scripts.function_tracer_pcode.authority.contracts import CauseIdV2

    key_fields = {field.name for field in fields(CauseAttributionKey)}
    create_params = set(
        inspect.signature(CauseIdV2.create).parameters
    ) - {"cls", "_factory_token"}
    assert create_params - {"identity_scope"} <= key_fields
    assert key_fields == create_params | {"target_kind", "proof_requirement_ids"}
