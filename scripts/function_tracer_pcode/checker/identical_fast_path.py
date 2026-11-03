# -*- coding: utf-8 -*-
"""同一バイナリ・同一関数の identity 評価と fast path（Issue #15）。

`EquivalenceChecker` が pair の解析を始める前に 1 度だけ呼ばれる。ここでやるのは
2 つのことだけで、両者は分かれている:

1. **identity の評価**（`--no-identical-fast-path` と無関係）。session の入力
   identity が左右同じ sha256 で関数名も同じ pair について、左右の Program から
   `ghidra.function_identity` で identity を観測し、一致するかを判定する。結果は
   `disposition`（なぜ適用可能/不可能か）と `identities` として返す。
2. **fast path の適用**（flag が ON で 1 の結果が適用可能なときだけ）。session に
   束縛した proof artifact を作り、既存の `EQ_CLOSURE` decisive event を 1 回出す。
   EQUIVALENT を決めるのは従来どおり `finalize_decision` で、ここはその根拠を
   1 つ足すだけ。

state は戻り値だけで運ぶ（checker の属性には何も置かない）。同じ checker
instance を次の pair で使い回しても、前の pair の評価は残らない。

evidence の保存条件は「左右それぞれの Program SHA が、**その側の** session 入力
SHA と一致した」こと。左右の Program SHA が互いに一致していても session 入力と
違うなら identity evidence は保存しない（後段の gate が同一関数と誤認しないため）。
"""

from __future__ import annotations

import time
from dataclasses import asdict, dataclass
from typing import Any, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.ghidra.function_identity import (
    BinaryFunctionIdentity,
    FunctionIdentityUnavailable,
    resolve_binary_function_identity,
)


_SHA256_HEX_DIGITS = frozenset("0123456789abcdef")

#: fast path で確定した結果の stage 名。
IDENTICAL_FUNCTION_IDENTITY_STAGE = "IDENTICAL_FUNCTION_IDENTITY"

#: fast path の authority が成立しなかったときの ERROR message。
IDENTICAL_FUNCTION_IDENTITY_AUTHORITY_INVALID = (
    "identical_function_identity_authority_invalid"
)

#: 結果 JSON の `identical_function_identity_evidence` の schema。
IDENTICAL_FUNCTION_IDENTITY_EVIDENCE_SCHEMA = (
    "identical_function_identity_evidence_v1"
)

#: fast path で確定した結果の `function*_identity` の schema。
IDENTICAL_FAST_PATH_FUNCTION_IDENTITY_SCHEMA = (
    "identical_fast_path_function_identity_v1"
)


def identity_evidence_payload(
    left: BinaryFunctionIdentity, right: BinaryFunctionIdentity,
) -> Mapping[str, Any]:
    """左右の identity 観測そのもの（gate が同一関数を確認するための evidence）。

    field を列挙し直さない（`BinaryFunctionIdentity` が正本）。ここは
    `function*_identity` とは**別の key** に載る: あちらは結果を他と区別する
    stable な識別子で、同じ binary を共有する別 pair と衝突してはいけない。
    """

    return {
        "schema": IDENTICAL_FUNCTION_IDENTITY_EVIDENCE_SCHEMA,
        "left": asdict(left),
        "right": asdict(right),
    }


def fast_path_function_identity(
    identity: BinaryFunctionIdentity, binary_id: str,
) -> Tuple[Any, ...]:
    """fast path で確定した結果の、その側だけを指す識別子。

    fast path は解析をしないので解析由来の identity が無い。binary 由来の観測は
    左右で同じ値になるため、それだけでは「B2 対 B3」と「B2 対 B4」を区別できず、
    `root_blocker_summary` の stable result key が衝突する。side を決めるのは
    binary ID なので、それを含めて識別子にする。
    """

    return (
        IDENTICAL_FAST_PATH_FUNCTION_IDENTITY_SCHEMA,
        ("binary_id", binary_id),
        identity.as_tuple(),
    )


@dataclass(frozen=True)
class IdenticalIdentityAssessment:
    """1 pair 分の identity 評価。`fast_path_result` があればそれで確定する。"""

    identities: Tuple[Optional[BinaryFunctionIdentity], Optional[BinaryFunctionIdentity]]
    disposition: Mapping[str, Any]
    fast_path_result: Any = None
    identity_evidence_ok: bool = False


def _disposition(reason: str, **extra: Any) -> Mapping[str, Any]:
    return {"applicable": False, "applied": False, "reason": reason, **extra}


#: operational な content identity の接頭辞。
_SHA256_PREFIX = "sha256:"


def _session_content_identity(value: Any) -> Optional[Tuple[str, str]]:
    """session 入力を `(operational identity, sha256 hex)` へ正規化する。

    正規化は `production_boundary` の 1 つだけを使う（Program ↔ sha の binding も
    encoder 側の照合も同じ関数で作られるので、ここで別実装を持たない）。ただし
    その関数は「非空の文字列はそのまま通す」ので、`sha256:<hex>` の形であること
    は**ここで確かめる**。接頭辞を確かめずに切り出すと、別形式の identity から
    偽の sha を取り出してしまう。形が違えば `None`（= 不適用）。
    """

    from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
        _operational_binary_content_identity,
    )

    try:
        identity = _operational_binary_content_identity(value)
    except ValueError:
        return None
    if not identity.startswith(_SHA256_PREFIX):
        return None
    digest = identity[len(_SHA256_PREFIX):]
    if len(digest) != 64 or not set(digest) <= _SHA256_HEX_DIGITS:
        return None
    return identity, digest


def _program_binding_is_bound(
    session: Any, program: Any, content_identity: str,
) -> bool:
    """`operational_program_binary_identities` がこの Program を sha に束縛しているか。"""

    bindings = session.domain_signal_state.get("operational_program_binary_identities")
    if not isinstance(bindings, Mapping):
        return False
    return bindings.get(id(program)) == content_identity


def _missing_binding_input(
    binary1_id: Any, binary2_id: Any, payload: Mapping[str, Any],
) -> Optional[str]:
    """artifact を束縛できない入力があればその理由を返す（無ければ `None`）。

    binary ID は checker 側の引数と session payload の両方で同じ非空文字列で
    なければならない（片側で閉じた確認にしないため）。
    """

    for value in (binary1_id, binary2_id):
        if type(value) is not str or not value:
            return "binary_id_unavailable"
    if (
        binary1_id != payload.get("binary1_id")
        or binary2_id != payload.get("binary2_id")
    ):
        return "binary_id_unavailable"
    contract_id = payload.get("observation_contract_id")
    if type(contract_id) is not str or not contract_id:
        return "observation_contract_unavailable"
    return None


def _resolve_side(program: Any, function_name: str):
    """(identity, 不適用理由) を返す。理由が None なら name が一意に解決できた。"""

    try:
        identity = resolve_binary_function_identity(program, function_name)
    except FunctionIdentityUnavailable:
        return None, "identity_unavailable"
    if identity.match_count == 0:
        return identity, "function_missing"
    if identity.match_count != 1:
        return identity, "name_not_unique"
    return identity, None


def assess_identical_function_identity(
    checker: Any,
    program1: Any,
    program2: Any,
    function_name1: str,
    function_name2: str,
    *,
    binary1_id: Optional[str],
    binary2_id: Optional[str],
    start_time: float,
) -> Optional[IdenticalIdentityAssessment]:
    """identity を評価し、適用できるなら fast path の結果まで作って返す。

    identical でない pair（session 入力 sha が違う / 関数名が違う）では `None` を
    返し、結果 JSON には何も足さない。
    """

    from scripts.function_tracer_pcode.authority.lifecycle.production_context import (
        active_production_pilot_session,
    )

    session = active_production_pilot_session()
    if session is None:
        return None
    payload = dict(getattr(session, "execution_payload", None) or ())
    left_input = _session_content_identity(payload.get("binary1_content_identity"))
    right_input = _session_content_identity(payload.get("binary2_content_identity"))
    if left_input is None or right_input is None or left_input != right_input:
        return None
    if function_name1 != function_name2:
        return None
    (left_identity, left_sha), (right_identity, right_sha) = left_input, right_input

    if not _program_binding_is_bound(
        session, program1, left_identity
    ) or not _program_binding_is_bound(session, program2, right_identity):
        return IdenticalIdentityAssessment(
            identities=(None, None),
            disposition=_disposition("program_binding_missing"),
        )

    left, left_reason = _resolve_side(program1, function_name1)
    right, right_reason = _resolve_side(program2, function_name2)
    if left_reason is not None or right_reason is not None:
        # 左右で理由が違うときは左側のものを載せる（`reason` は 1 つ）。
        return IdenticalIdentityAssessment(
            identities=(None, None),
            disposition=_disposition(left_reason or right_reason),
        )

    # 左右それぞれの Program SHA を、その側の session 入力 SHA と直接照合する。
    # 「左右の Program が互いに同じ」だけでは、比較対象のバイナリと同じである
    # ことにならない。
    sha_mismatch = tuple(
        side for side, identity, expected in (
            ("left", left, left_sha), ("right", right, right_sha),
        ) if identity.executable_sha256 != expected
    )
    if sha_mismatch:
        return IdenticalIdentityAssessment(
            identities=(None, None),
            disposition=_disposition(
                "identity_mismatch",
                sha_mismatch_side=(
                    "both" if len(sha_mismatch) == 2 else sha_mismatch[0]
                ),
            ),
        )
    # 比較する field を 2 箇所で数え上げない（`as_tuple()` が正本。ここに来る
    # 時点で両側とも `match_count == 1` なので、schema と件数も一致する）。
    if left.as_tuple() != right.as_tuple():
        return IdenticalIdentityAssessment(
            identities=(None, None),
            disposition=_disposition("identity_mismatch"),
        )

    # artifact の binding は checker 側が持つ値で作り、encoder は session 側の
    # payload から作り直して照合する。片方が欠けていれば束縛が作れないので
    # 適用しない（fail closed）。
    binding_gap = _missing_binding_input(binary1_id, binary2_id, payload)
    if binding_gap is not None:
        # identity 自体は照合済みなので evidence は残す。束縛できないのは
        # artifact の方（fast path を適用しないだけ）。
        return IdenticalIdentityAssessment(
            identities=(left, right),
            disposition=_disposition(binding_gap),
            identity_evidence_ok=True,
        )

    if not getattr(checker, "identical_fast_path", False):
        return IdenticalIdentityAssessment(
            identities=(left, right),
            disposition={"applicable": True, "applied": False, "reason": "disabled"},
            identity_evidence_ok=True,
        )

    # Issue #282 (I12): この EQ は「同じ program を同じ状態で呼ぶ」ことを前提にする。前提が D に入っていなければ
    # 無条件の EQ にしない（fast path を適用せず通常の解析へ進む）
    from scripts.function_tracer_pcode.proof.formula.input_correspondence.memory_policy import (
        IDENTICAL_BINARY_PREMISES,
        premises_admit_unconditional_eq,
    )

    if not premises_admit_unconditional_eq(IDENTICAL_BINARY_PREMISES):
        return IdenticalIdentityAssessment(
            identities=(left, right),
            disposition={"applicable": True, "applied": False, "reason": "memory_premise_not_admitted"},
            identity_evidence_ok=True,
        )

    fast_path_result = _apply_fast_path(
        session,
        program1,
        program2,
        left,
        right,
        binary1_id=binary1_id,
        binary2_id=binary2_id,
        observation_contract_id=payload["observation_contract_id"],
        start_time=start_time,
    )
    if fast_path_result.error_message is not None:
        return IdenticalIdentityAssessment(
            identities=(left, right),
            disposition={
                "applicable": True,
                "applied": False,
                "reason": "authority_invalid",
            },
            fast_path_result=fast_path_result,
            identity_evidence_ok=True,
        )
    return IdenticalIdentityAssessment(
        identities=(left, right),
        disposition={"applicable": True, "applied": True, "reason": "applied"},
        fast_path_result=fast_path_result,
        identity_evidence_ok=True,
    )


def _session_binding_for(
    session: Any,
    left: BinaryFunctionIdentity,
    *,
    binary1_id: str,
    binary2_id: str,
    observation_contract_id: str,
):
    """artifact を「この実行のこの pair・この関数」へ束縛する事実を組む。

    ここで組むのは checker 側が持つ値で、encoder は session 側の
    `execution_payload` から同じものを組み直して照合する（片側だけで閉じた
    確認にしない）。
    """

    from scripts.function_tracer_pcode.authority.domains.identical_function_identity import (
        IdenticalFunctionIdentitySessionBinding,
    )

    return IdenticalFunctionIdentitySessionBinding(
        result_occurrence_id=session.identity.result_occurrence_id,
        execution_identity_digest=session.identity.execution_identity_digest,
        left_binary_id=binary1_id,
        right_binary_id=binary2_id,
        binary_content_identity=f"sha256:{left.executable_sha256}",
        function_name=left.function_name,
        observation_contract_id=observation_contract_id,
    )


def _apply_fast_path(
    session: Any,
    program1: Any,
    program2: Any,
    left: BinaryFunctionIdentity,
    right: BinaryFunctionIdentity,
    *,
    binary1_id: str,
    binary2_id: str,
    observation_contract_id: str,
    start_time: float,
):
    """artifact を作り decisive event を 1 回出す。出せなければ ERROR 結果を返す。

    authority が成立しないときに EQUIVALENT を返さないことがこの関数の要点。
    `ValueError` / `TypeError` は「authority の構成が拒否された」ことなので、
    握り潰さずに `error_message` と `failure_message` を持つ ERROR 結果へ変える
    （boundary の legacy ERROR 経路が canonical ERROR として保存する）。
    """

    from scripts.function_tracer_pcode.authority.domains.identical_function_identity import (
        IdenticalFunctionIdentitySignal,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        emit_identical_function_identity_signal,
    )
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult
    from scripts.function_tracer_pcode.smt import ParallelResult
    from scripts.function_tracer_pcode.proof.formula.input_correspondence.memory_policy import (
        IDENTICAL_BINARY_PREMISES,
        premise_record,
    )

    binary1_name = program1.getName() if hasattr(program1, "getName") else "binary1"
    binary2_name = program2.getName() if hasattr(program2, "getName") else "binary2"

    def _authority_invalid(detail: str):
        return EquivalenceResult(
            is_equivalent=None,
            function1_name=left.function_name,
            function2_name=right.function_name,
            binary1_name=binary1_name,
            binary2_name=binary2_name,
            solver_results=ParallelResult(results=[]),
            total_time=time.time() - start_time,
            error_message=IDENTICAL_FUNCTION_IDENTITY_AUTHORITY_INVALID,
            failure_status="strategy_exception",
            failure_message=detail,
            stage_path=[IDENTICAL_FUNCTION_IDENTITY_STAGE],
        )

    try:
        binding = _session_binding_for(
            session,
            left,
            binary1_id=binary1_id,
            binary2_id=binary2_id,
            observation_contract_id=observation_contract_id,
        )
        signal = IdenticalFunctionIdentitySignal.issue(
            left, right, session_binding=binding
        )
        artifact = signal.artifact
        emitted = emit_identical_function_identity_signal(
            signal, producer_site_manifest_id="checker-identical-function-identity",
        )
    except (TypeError, ValueError) as exc:
        return _authority_invalid(f"{type(exc).__name__}: {exc}")
    if emitted != 1:
        return _authority_invalid(
            f"identical function identity proof emitted {emitted} decisive events"
        )
    return EquivalenceResult(
        is_equivalent=True,
        function1_name=left.function_name,
        function2_name=right.function_name,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        solver_results=ParallelResult(results=[]),
        total_time=time.time() - start_time,
        stage_path=[IDENTICAL_FUNCTION_IDENTITY_STAGE],
        function1_identity=fast_path_function_identity(left, binary1_id),
        function2_identity=fast_path_function_identity(right, binary2_id),
        decisive_proof_provenance={
            "kind": "identical_function_identity",
            "proof_artifact_digest": artifact.artifact_digest,
            "artifact": dict(artifact.body),
            # Issue #282 (I12): この EQ が使った memory の前提と、方針表の扱い
            "memory_premises": [list(row) for row in premise_record(IDENTICAL_BINARY_PREMISES)],
        },
    )


def attach_identity_assessment(
    result: Any, assessment: Optional[IdenticalIdentityAssessment],
) -> Any:
    """結果へ identity evidence と disposition を 1 箇所で載せる。

    `function*_identity` には触らない。あれは解析が作る stable result key で、
    左右・pair を区別する責務がある。同一性の観測は
    `identical_function_identity_evidence` に載せ、gate はそちらを読む。
    """

    if assessment is None or result is None:
        return result
    result.identical_fast_path_disposition = dict(assessment.disposition)
    if assessment.identity_evidence_ok:
        left, right = assessment.identities
        if left is not None and right is not None:
            result.identical_function_identity_evidence = identity_evidence_payload(
                left, right
            )
    return result
