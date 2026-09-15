# -*- coding: utf-8 -*-
"""Issue #15 PR-15-B: identity evidence と stable result key を混ぜない。

PR-15-A は SHA 照合済みの identical pair について `function*_identity` を
binary 由来の identity（左右で同じ値）で上書きしていた。`function*_identity` は
`reporting/root_blocker_summary` が結果を一意に指すための key でもあるので、
同じ sample・同じ関数・同じ sha を共有する複数 pair（`airy/Sign` の
B2_B3 / B2_B4 / B3_B4 は B2 = B3 = B4）が 1 つの `StableResultRef` に潰れ、
`duplicate_current_result_occurrence` として **全件が active 集計から外れる**。

fast path OFF の run を pre-15 の oracle として使う以上これは許容できないので、
PR-15-B は 2 つの key を分ける:

* `function*_identity` = その結果の側を他と区別する識別子（解析由来。fast path で
  確定した結果では binary ID を含む識別子）。
* `identical_function_identity_evidence` = 左右が同じ関数だと言える観測（gate が
  読む）。

この file はその分離を契約として固定する。
"""
from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.checker.identical_fast_path import (
    IdenticalIdentityAssessment,
    attach_identity_assessment,
    fast_path_function_identity,
    identity_evidence_payload,
)
from scripts.function_tracer_pcode.ghidra.function_identity import (
    BinaryFunctionIdentity,
)
from scripts.function_tracer_pcode.reporting.root_blocker_summary import (
    summarize_root_blockers,
)
from scripts.function_tracer_pcode.tests.unit.test_root_blocker_summary import (
    _attempt,
    _payload,
    _reason,
)

SHA = "c" * 64


def _identity(name: str = "snippet") -> BinaryFunctionIdentity:
    return BinaryFunctionIdentity(
        executable_sha256=SHA,
        function_name=name,
        language_id="AARCH64:LE:64:v8A",
        compiler_spec_id="default",
        image_base=0x100000,
        entry=("ram", 0x100000),
        body_range=(("ram", 0x100000), ("ram", 0x100027)),
        match_count=1,
    )


class _Result:
    """`EquivalenceResult` のうち attach が触る field だけを持つ器。"""

    def __init__(self, left_identity=None, right_identity=None):
        self.function1_identity = left_identity
        self.function2_identity = right_identity
        self.identical_fast_path_disposition = None
        self.identical_function_identity_evidence = None


def _assessment(**kwargs) -> IdenticalIdentityAssessment:
    left, right = _identity(), _identity()
    return IdenticalIdentityAssessment(
        identities=(left, right),
        disposition={"applicable": True, "applied": False, "reason": "disabled"},
        identity_evidence_ok=True,
        **kwargs,
    )


def test_attaching_identity_evidence_does_not_touch_the_stable_result_key():
    analysis_left = ("function_identity", ("binary_id", "B2"), "snippet")
    analysis_right = ("function_identity", ("binary_id", "B3"), "snippet")
    result = _Result(analysis_left, analysis_right)

    attach_identity_assessment(result, _assessment())

    assert result.function1_identity == analysis_left
    assert result.function2_identity == analysis_right
    evidence = result.identical_function_identity_evidence
    assert evidence["schema"] == "identical_function_identity_evidence_v1"
    assert evidence["left"] == evidence["right"]
    assert evidence["left"]["executable_sha256"] == SHA
    assert evidence["left"]["match_count"] == 1


def test_identity_evidence_is_not_written_without_a_verified_observation():
    result = _Result()
    attach_identity_assessment(
        result,
        IdenticalIdentityAssessment(
            identities=(None, None),
            disposition={
                "applicable": False, "applied": False, "reason": "identity_mismatch",
            },
        ),
    )
    assert result.identical_function_identity_evidence is None
    assert result.identical_fast_path_disposition["reason"] == "identity_mismatch"


def test_evidence_payload_enumerates_every_observed_field_once():
    left = _identity()
    payload = identity_evidence_payload(left, _identity())
    assert set(payload["left"]) == {
        "executable_sha256", "function_name", "language_id", "compiler_spec_id",
        "image_base", "entry", "body_range", "match_count",
    }
    assert payload["left"]["entry"] == ("ram", 0x100000)


def test_a_fast_path_identity_names_its_own_side():
    left = fast_path_function_identity(_identity(), "B2")
    right = fast_path_function_identity(_identity(), "B3")
    assert left != right
    assert left[:2] == (
        "identical_fast_path_function_identity_v1", ("binary_id", "B2"),
    )
    assert left[2] == _identity().as_tuple()


def _pair_payload(left_id: str, right_id: str, *, fast_path: bool):
    """同じ byte 同一 binary を共有する 1 pair の final UNKNOWN 結果。"""

    payload = _payload(
        run=f"run-{left_id}-{right_id}",
        case="snippet",
        attempts=[_attempt(0, [_reason("unresolved_expression")])],
    )
    # 左右のバイナリは byte 同一なので comparison domain は 3 pair で同じ。
    payload["binary1_content_identity"] = ("sha256", SHA)
    payload["binary2_content_identity"] = ("sha256", SHA)
    if fast_path:
        payload["function1_identity"] = fast_path_function_identity(_identity(), left_id)
        payload["function2_identity"] = fast_path_function_identity(_identity(), right_id)
    else:
        payload["function1_identity"] = ("function_identity", ("binary_id", left_id), "snippet")
        payload["function2_identity"] = ("function_identity", ("binary_id", right_id), "snippet")
    return payload


PAIRS = (("B2", "B3"), ("B2", "B4"), ("B3", "B4"))


@pytest.mark.parametrize("fast_path", [False, True])
def test_pairs_sharing_one_binary_stay_separate_results(fast_path: bool):
    payloads = [_pair_payload(left, right, fast_path=fast_path) for left, right in PAIRS]

    summary = summarize_root_blockers(payloads)

    assert "duplicate_current_result_occurrence" not in summary.diagnostics
    assert "ambiguous_snapshot_membership" not in summary.diagnostics
    assert "missing_function_identity" not in summary.diagnostics
    occurrences = {
        occurrence
        for blocker in summary.active_root_blockers
        for occurrence in blocker.affected_result_occurrences
    }
    assert len(occurrences) == len(PAIRS)


def test_a_side_independent_identity_would_collapse_every_such_pair():
    """分離しないとどうなるかを、退行時に落ちる形で固定する。

    左右とも同じ binary 由来 identity を入れると（= PR-15-A の形）3 pair が 1 つの
    `StableResultRef` になり、曖昧として **3 件とも** active から外れる。
    """

    shared = _identity().as_tuple()
    payloads = []
    for left, right in PAIRS:
        payload = _pair_payload(left, right, fast_path=False)
        payload["function1_identity"] = shared
        payload["function2_identity"] = shared
        payloads.append(payload)

    summary = summarize_root_blockers(payloads)

    assert summary.diagnostics["duplicate_current_result_occurrence"] == 1
    assert summary.active_root_blockers == ()
