# -*- coding: utf-8 -*-
"""Issue #54-A: result surface から `rewrite_info` / `RewriteInfo` が消えたこと、
および `rewrite_info` は serialization surface にしか影響せず semantic projection には
影響しないことを固定する。

`rewrite_info` は常に `{"applied": false, "function1_rewrites": [], "function2_rewrites": []}`
という定数で、解析結果を変えたことは一度もない（rewrite 段階は廃止済み）。したがって
削除で変わるのは JSON / Python surface と、その全体を入力にする preimage 系 digest だけ
である。判定の意味を射影する `semantic_projection_digest` は `rewrite_info` を読まない。

digest test は「旧 surface 入りの payload」と「新 surface の payload」を **2 本独立に
finalize** して比べる（`test_unknown_taxonomy_v2_phase8_cutover.py` の
`build_canonical_result_finalization_bundle` 利用を雛形にした）。片方の bundle を加工して
他方を作る方法は採らない。消費済みの session / finalization 状態も再利用しない。
"""
import inspect

import pytest

from scripts.function_tracer_pcode.checker.debug_trace import (
    Attempt,
    DebugTrace,
    TransitionReason,
)
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.tests.unit._finalization_support import (
    _independent_finalization,
)


def _attempt(**overrides):
    fields = dict(
        attempt_id=0,
        retry_count=0,
        phase="P0_BASE",
        stage_path=["S_PAIRWISE"],
        strategy="pairwise",
        result=None,
        transition_reason=TransitionReason.UNKNOWN.value,
    )
    fields.update(overrides)
    return Attempt(**fields)


def _equivalence_result(**overrides):
    fields = dict(
        is_equivalent=True,
        function1_name="f",
        function2_name="f",
        binary1_name="left",
        binary2_name="right",
        solver_results=None,
    )
    fields.update(overrides)
    return EquivalenceResult(**fields)

# Issue #54-A 以前に result JSON へ出ていた定数。旧 surface の再現に使う。
LEGACY_REWRITE_INFO = {
    "applied": False,
    "function1_rewrites": [],
    "function2_rewrites": [],
}


# --------------------------------------------------------------------------
# 1. digest 分離: preimage digest は変わるが semantic projection は変わらない
# --------------------------------------------------------------------------

def test_rewrite_info_changes_the_payload_preimage_but_not_the_semantic_projection(
    tmp_path, monkeypatch,
):
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        validate_canonical_result_finalization_bundle,
    )

    bundle_key = tmp_path / "canonical-bundle.key"
    bundle_key.write_bytes(b"k" * 32)
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID", "issue54a-test-key")
    monkeypatch.setenv("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE", str(bundle_key))
    monkeypatch.setenv(
        "UNKNOWN_TAXONOMY_V2_RESULT_ENTRY_OCCURRENCE_NONCE", "issue54a-occurrence"
    )

    # 旧 surface は top-level と debug_trace.attempts[] の両方に `rewrite_info` を
    # 持っていたので、attempts[] が入る result を作る。
    def _result_with_attempt():
        trace = DebugTrace()
        trace.add_attempt(_attempt())
        return _equivalence_result(debug_trace=trace)

    result_a = _result_with_attempt()
    result_b = _result_with_attempt()

    # A: Issue #54-A 後の surface そのまま。
    payload_a = result_a.to_dict()
    # B: 旧 surface の再現。top-level と debug_trace.attempts[] の両方に
    #    `rewrite_info` を戻す（削除したのはこの 2 箇所）。
    payload_b = result_b.to_dict()
    payload_b["rewrite_info"] = dict(LEGACY_REWRITE_INFO)
    attempts_b = (payload_b.get("debug_trace") or {}).get("attempts")
    assert isinstance(attempts_b, list) and attempts_b, "debug_trace.attempts[] が空では旧 surface を再現できない"
    for attempt in attempts_b:
        attempt["rewrite_info"] = dict(LEGACY_REWRITE_INFO)

    # 2 つの payload の差は `rewrite_info` キーだけであること（これが無いと
    # semantic projection 一致の assert が「他も同じだから当然」になってしまう）。
    assert payload_a != payload_b
    stripped_b = {k: v for k, v in payload_b.items() if k != "rewrite_info"}
    stripped_b["debug_trace"] = {
        **payload_b["debug_trace"],
        "attempts": [
            {k: v for k, v in attempt.items() if k != "rewrite_info"}
            for attempt in payload_b["debug_trace"]["attempts"]
        ],
    }
    assert stripped_b == payload_a

    bundle_a, session_a, evidence_a = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue54a-new-surface", result_payload_preimage=payload_a,
    )
    bundle_b, session_b, evidence_b = _independent_finalization(
        tmp_path, monkeypatch,
        case_id="issue54a-legacy-surface", result_payload_preimage=payload_b,
    )
    # 2 本は独立な finalization であること: session / evidence / bundle のどれも
    # 共有しておらず、片方を加工して他方を作っていない。
    assert session_a is not session_b
    assert evidence_a is not evidence_b
    assert evidence_a.pilot_result is not evidence_b.pilot_result
    assert bundle_a is not bundle_b
    assert bundle_a["bundle_digest"] != bundle_b["bundle_digest"]

    for bundle, preimage in ((bundle_a, payload_a), (bundle_b, payload_b)):
        validated = validate_canonical_result_finalization_bundle(
            bundle,
            result_payload_preimage=preimage,
            bundle_verification_key_id="issue54a-test-key",
            bundle_verification_key=b"k" * 32,
        )
        assert validated["outcome"] == "EQUIVALENT"

    # serialization surface が違うので preimage digest は違う。
    assert (
        bundle_a["canonical_result_payload_preimage_digest"]
        != bundle_b["canonical_result_payload_preimage_digest"]
    )
    # 意味の射影は `rewrite_info` を読まないので同じ。
    assert (
        bundle_a["canonical_semantic_result_projection"]["semantic_projection_digest"]
        == bundle_b["canonical_semantic_result_projection"]["semantic_projection_digest"]
    )
    assert (
        bundle_a["canonical_semantic_result_projection"]["payload"]
        == bundle_b["canonical_semantic_result_projection"]["payload"]
    )
    # 射影が空でないこと（一致が vacuous でない確認）。
    projection = bundle_a["canonical_semantic_result_projection"]["payload"]
    assert projection["canonical_outcome"] == "EQUIVALENT"
    assert "rewrite_info" not in projection


# --------------------------------------------------------------------------
# 2. surface 不在
# --------------------------------------------------------------------------

def test_result_json_has_no_rewrite_info_key():
    assert "rewrite_info" not in _equivalence_result().to_dict()


def test_result_object_has_no_rewrite_info_attribute():
    assert not hasattr(_equivalence_result(), "rewrite_info")


def test_attempt_json_has_no_rewrite_info_key():
    attempt = _attempt()
    assert "rewrite_info" not in attempt.to_dict()
    assert not hasattr(attempt, "rewrite_info")


def test_debug_trace_attempts_json_has_no_rewrite_info_key():
    trace = DebugTrace()
    trace.add_attempt(_attempt())
    for attempt in trace.to_dict()["attempts"]:
        assert "rewrite_info" not in attempt


def test_checker_package_no_longer_exports_rewrite_info():
    from scripts.function_tracer_pcode import checker

    assert "RewriteInfo" not in checker.__all__
    assert "RewriteInfo" not in checker._LAZY
    with pytest.raises(AttributeError):
        getattr(checker, "RewriteInfo")


def test_attempt_and_result_assembly_signatures_have_no_rewrite_info():
    from scripts.function_tracer_pcode.checker.attempts import record_attempt
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
    from scripts.function_tracer_pcode.checker.result_assembly import (
        assemble_equivalence_result,
    )

    for surface in (
        record_attempt,
        EquivalenceChecker._record_attempt,
        assemble_equivalence_result,
    ):
        assert "rewrite_info" not in inspect.signature(surface).parameters, surface


def test_result_module_no_longer_depends_on_the_rewrite_package():
    """`RewriteInfo` が消えたので `RewriteResult` の import も不要（#54-B の前提）。

    固定するのは「旧 rewrite package への依存が無い」ことだけで、`rewrite` という
    単語一般を将来禁止はしない（pairwise / proof 層には無関係な同名識別子がある）。
    """
    from scripts.function_tracer_pcode.checker import result as result_module

    source = inspect.getsource(result_module)
    assert "RewriteResult" not in source
    assert "semantics.transform.rewrite" not in source
