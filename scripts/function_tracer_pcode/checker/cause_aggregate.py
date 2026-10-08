# -*- coding: utf-8 -*-
"""UNKNOWN 原因の可逆な compact 集計（Issue #128 PR-128-A）。

`debug_trace` は結果 JSON の約 30% を占めるが、原因分析（root blocker /
backlog / completion / causal transition）の唯一の入力でもある。将来
`--debug` 時だけ添付するようにしても分析を失わないよう、**reporting が必要と
する集計と identity だけ**を先にここで作り、`EquivalenceResult.to_dict()` の
`unknown_cause_aggregate` として常時出す。

契約:

* full `debug_trace` の複製は作らない。record 本体・solver 行・SMT は持たない。
* **最終 UNKNOWN reason 件数の正本は canonical payload（`unknown_reasons`）**。
  `final_reasons` は canonical が確定しているときだけ作る集計キャッシュで、
  未確定の legacy 値を canonical として書かない。
* 値を持てないブロックは `null`（= unknown）にする。実際に 0 件だったことと
  区別できなくなるため 0 や `{}` で埋めない。`evidence_present` が根拠。
* 判定には一切効かない。`_semantic_projection` はこのブロックを読まないが、
  `to_dict()` には入るので canonical result payload preimage は変わり得る
  （`checker/diagnostics.py` の digest 契約と同じ）。

この module は reporting（`root_blocker_summary` / `unknown_reason_summary`）と
**同じ関数**を共有する。checker から reporting を import しないための配置で、
集計の定義が 2 箇所に分かれてドリフトするのを防ぐ。

schema `unknown-cause-aggregate-v1` の block:

* `final_reasons` / `legacy_view`: 1 つの record 集合の集計（`build_reason_view`）。
  前者は canonical 確定時のみ。後者は **trace を観測できたときだけ**で、
  `source` が `final_attempt` / `payload_records` のどちらを選んだかを言う。
  trace がもともと無い結果では `null`（= 診断の証拠が無い）。
* `effective_source` / `backlog` / `operational`: 上の 2 つのうち authority が
  選ぶ側（canonical > legacy）の backlog 4 次元と operational 2 次元。
* `completions` / `transitions`: 完了・因果遷移イベントの集計。backlog とは
  独立に数える（完了件数から未完了を引かない）。
* `root_causes[]`: root blocker identity ごとの `all` / `active` union。
  `active` は「最終 attempt かつ実効 causal status が active」な occurrence だけ。
  `reason_id` / `decision_effect` は読みやすさのための代表値で、集合そのものは
  `all.reason_ids` / `all.decision_effects` にある。
* `identity_pool`: 繰り返す identity の実体。`*_refs` はこの index。
* `root_cause_stats`: reporting の coverage / diagnostics を再構成する counter。
* `attempts` / `evidence_present`: attempt の要約と、各 block の観測可否。
  `evidence_present` は各 block を **観測できたか**（件数ではない）。
  `debug_trace` は「この結果に trace があったか」の証言で、consumer が
  「trace が省かれた」と「もともと無かった」を区別するのに使う。
"""

from __future__ import annotations

import hashlib
import json
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core import json_encoding, live_values
from scripts.function_tracer_pcode.core.structural import (
    cross_process_node,
    key_contains_unidentified,
    key_is_process_independent,
)
from scripts.function_tracer_pcode.core.json_encoding import (
    CANONICAL,
    LEGACY,
    NOT_PLAIN as _NOT_PLAIN_SCALAR,
    builtin_str,
    builtin_view,
    copy_legacy_containers,
    exception_text,
    plain_scalar,
    is_json_record,
    materialize,
    value_token,
)
from scripts.function_tracer_pcode.core.live_values import (
    as_bool,
    as_int,
    as_str,
    attribute,
    builtin_mapping,
    builtin_sequence,
    elements_of,
    items_of,
    json_scalar,
    lookup,
    size,
)

from scripts.function_tracer_pcode.checker.unknown_reason import (
    UnknownReasonRecord,
    build_unknown_recovery_actions,
    coerce_unknown_reason_record,
    coerce_unknown_reason_records,
)
from scripts.function_tracer_pcode.proof.cause_identity import (
    CauseKey,
    IdentityScope,
    ProofRequirementId,
    canonical_cause_tuple,
    cause_key_from_dict,
)
from scripts.function_tracer_pcode.proof.unknown_reason import (
    UNKNOWN_TUPLE_MISSING,
    UnknownCountKind,
    UnknownDecisionEffect,
    UnknownReasonClass,
    UnknownReasonId,
    UnknownRecoveryActionStatus,
)


UNKNOWN_CAUSE_AGGREGATE_SCHEMA = "unknown-cause-aggregate-v1"

FINAL_UNKNOWN_TRANSITIONS = frozenset({"UNKNOWN", "TIMEOUT"})
# `global_reason_tuple_from_record` / `_from_action` が作る tuple の次元数。
# 古い artifact の tuple を読むとき、consumer はこの幅へ正規化する。
GLOBAL_REASON_TUPLE_WIDTH = 7
PROOF_BACKLOG_CLASSES = frozenset({
    UnknownReasonClass.PROOF_OBLIGATION.value,
    UnknownReasonClass.COVERAGE_GAP.value,
})
BLOCKING_DECISION_EFFECTS = frozenset({
    "blocks_equivalence",
    "blocks_disequivalence",
    "blocks_decision",
    "retryable",
})
PRIMARY_DECISION_EFFECT_PRIORITY = {
    UnknownDecisionEffect.BLOCKS_EQUIVALENCE.value: 0,
    UnknownDecisionEffect.BLOCKS_DISEQUIVALENCE.value: 1,
    UnknownDecisionEffect.BLOCKS_DECISION.value: 2,
    UnknownDecisionEffect.RETRYABLE.value: 3,
    UnknownDecisionEffect.DIAGNOSTIC_ONLY.value: 4,
}
_ACTIVE_CAUSAL_STATUSES = frozenset({"active_final_blocker", "contributing_blocker"})
_RESOLVED_CAUSAL_STATUSES = frozenset({"discharged", "superseded"})

# 旧 `object_target_key` を typed cause identity に読み替える adapter。
# 登録済みの schema だけが「完全な tuple がそのスコープの意味的 identity を
# すでに持っている」ことを主張できる（未登録は `legacy_adapter_missing`）。
LEGACY_CAUSE_SCOPES = {
    "return_coverage": (IdentityScope.UNARY.value, "return_coverage_v3"),
    "call_argument_evidence": (IdentityScope.UNARY.value, "call_evidence_v1"),
    "call_target_resolution_evidence": (IdentityScope.UNARY.value, "call_evidence_v1"),
    "deferred_call_site": (IdentityScope.UNARY.value, "deferred_call_v1"),
    "return_width_bridge": (IdentityScope.RELATIONAL.value, "return_width_v1"),
    "solver_timeout": (IdentityScope.EXECUTION.value, "solver_timeout_v1"),
}


# ---------------------------------------------------------------------------
# identity の正規化（reporting と共有）
# ---------------------------------------------------------------------------

#: 今の集計が、構造 key の token を作った process 自身の値だけを読んでいるか（Issue #215
#: Gate A）。既定は偽（fail-closed: 結果 JSON など、別の process が書き得る値として扱う）。
_MINTING_PROCESS_SCOPE: ContextVar[bool] = ContextVar("cause_aggregate_minting_process", default=False)


@contextmanager
def minting_process_identities():
    """token を作った process 自身の結果を集計する間だけ、process 内の identity で比べる。

    構造 key の token は作った process の中では identity として正しい（C-K1）。その process
    の集計（`build_unknown_cause_aggregate`）がこの scope を張ると、`freeze_identity` は token
    を置き換えず、`resolve_cause_identity` も token を含む key を解決する。scope の外（既定）
    では、別の process が書いた値として扱い、token を何とも等しくならない印にする（過分割）。
    書き出した集計を読む側（reporting）は scope を張らないので、process をまたいで token を
    比べることは無い。
    """

    marker = _MINTING_PROCESS_SCOPE.set(True)
    try:
        yield
    finally:
        _MINTING_PROCESS_SCOPE.reset(marker)


def freeze_identity(value: Any) -> Any:
    """dict / list / tuple を比較可能な frozen 表現へ正規化する。

    JSON 往復で tuple が list になっても同じ値になるので、`debug_trace` 経路と
    `unknown_cause_aggregate` 経路の identity が一致する。

    Issue #22 PR-22-D: 組み込みの振る舞いの容器だけを辿り、葉は組み込みで書ける値（文字列・
    scalar・組み込みのままの enum）だけをそのまま残す。それ以外の葉（上書きした `__hash__` /
    `__repr__` を持ち得る live な object）は値で比べてよい決定的な印にする（`value_token`: enum は
    名前、dataclass は field）。field も持たない object だけが identity の印（旧実装の既定の `repr`
    と同じく object ごとに区別する）。JSON から読んだ値（reporting）は常に組み込みの値なので変わらない。

    Issue #215 Gate A: **結果 JSON から読んだ identity を process をまたいで比べる入口はこの関数**。
    既定では列の段ごとに `core.structural.cross_process_node` を通し、構造 key の tail token などの
    process の中でだけ意味を持つ値を、何とも等しくならない印に置き換える（過分割に倒す）。
    reporting が identity を作るときは、生の値を比べずにこの写しを使うこと。token を作った
    process 自身の集計（`minting_process_identities()` の中）だけは置き換えない。

    容器は `live_values` の `items_of` / `elements_of` だけで辿り、写しは package が組む tuple と
    owner が作る葉（`builtin_str` の key・`value_token`）だけから成る（写しは組み込みの値）。
    再帰せずに明示の段で辿る（深い入れ子で `RecursionError` にならない。閉路は `ValueError`）。
    """
    if builtin_mapping(value) is None and not builtin_sequence(value):
        return value_token(value)
    root: List[Any] = []
    # 辿っている容器の段: [子の iterator, 子の写し, mapping の key 列（列なら None）, 容器の id]
    frames: List[List[Any]] = []
    active: set = set()
    _freeze_enter(value, root, frames, active)
    promote = not _MINTING_PROCESS_SCOPE.get()
    while frames:
        frame = frames[-1]
        child = next(frame[0], _FROZEN_END)
        if child is _FROZEN_END:
            frames.pop()
            active.discard(frame[3])
            keys = frame[2]
            # 列は構造 key の token であり得る: process をまたぐ比較で一致しないよう、
            # 構造 identity の owner の規則を通す（Issue #215 Gate A）
            if keys is not None:
                frozen = tuple(zip(keys, frame[1]))
            else:
                frozen = cross_process_node(tuple(frame[1])) if promote else tuple(frame[1])
            (frames[-1][1] if frames else root).append(frozen)
            continue
        _freeze_enter(child, frame[1], frames, active)
    return root[0]


#: `freeze_identity` の段の子の終わり
_FROZEN_END = object()


def _freeze_enter(item: Any, out: List[Any], frames: List[List[Any]], active: set) -> None:
    """`item` の写しを `out` へ置く（葉）か、`item` の子を写す段を `frames` へ積む（容器）。"""

    mapping = builtin_mapping(item)
    if mapping is None and not builtin_sequence(item):
        # scalar の subclass（JPype の `JInt` など）は基底型の値、enum は名前、dataclass は field の印。
        # それ以外の live な object だけが identity の印（`value_token`）
        out.append(value_token(item))
        return
    marker = id(item)
    if marker in active:
        raise ValueError("cyclic identity value")
    active.add(marker)
    if mapping is not None:
        keys, children = _ordered_members(mapping)
        frames.append([elements_of(children), [], keys, marker])
    else:
        frames.append([elements_of(item), [], None, marker])


def _ordered_members(mapping: Any) -> Tuple[List[str], List[Any]]:
    """mapping の (key の文字列, 値) を key の文字列の順に（安定。同じ文字列は元の順）。"""

    keys: List[str] = []
    children: List[Any] = []
    for key, child in items_of(mapping):
        keys.append(builtin_str(key))
        children.append(child)
    order = sorted(range(len(keys)), key=keys.__getitem__)
    return [keys[index] for index in order], [children[index] for index in order]


def _in_key_order(values: Sequence[Any], keys: Sequence[Any]) -> List[Any]:
    """`values` を対応する `keys`（組み込みの値）の順に並べる（安定。`values` 自身は比べない）。"""

    order = sorted(range(len(keys)), key=keys.__getitem__)
    return [values[index] for index in order]


def identity_tuple(value: Any) -> Tuple[Any, ...]:
    frozen = freeze_identity(value)
    if frozen is None:
        return ()
    return frozen if isinstance(frozen, tuple) else (frozen,)


def identity_digest(value: Any) -> str:
    """identity の安定した digest（tuple/list の違いに依らない）。

    `freeze_identity` の写しは tuple と組み込みの葉だけなので、JSON の scalar でない葉
    （集合・組み込みのままの enum・`BoundedEvidence`・印の object）だけを `builtin_str` で書く
    （旧 `_jsonable` と同じ文字列）。
    """
    payload = json.dumps(
        freeze_identity(value),
        default=builtin_str,
        sort_keys=True,
        ensure_ascii=False,
        separators=(",", ":"),
    )
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class CauseIdentityResolution:
    """`typed_cause_key` / `object_target_key` から作った root blocker identity。"""

    identity_scope: Optional[str] = None
    cause_kind: Optional[str] = None
    canonical_cause_key: Optional[Tuple[Any, ...]] = None
    typed: bool = False
    diagnostic: Optional[str] = None

    @property
    def resolved(self) -> bool:
        return self.canonical_cause_key is not None


def resolve_cause_identity(
    *,
    typed_cause_key: Any,
    object_target_key: Any,
    left_binary_identity: Tuple[Any, ...],
    right_binary_identity: Tuple[Any, ...],
) -> CauseIdentityResolution:
    """reason record 1 件から root blocker identity を決める（純粋関数）。

    `diagnostic` は解決できなかった理由の counter 名で、呼び出し側が自分の
    diagnostics に加算する。identity を返さないことと counter は 1 対 1。

    Issue #22 PR-22-D: 返す identity は組み込みの値だけ（scope / kind は文字列、key は
    `freeze_identity` の写し。typed key の tuple は写しても同じ値）。

    Issue #215 Gate A: この identity は **別の process が書いた結果どうし**でも比べる
    （`reporting/root_blocker_summary` が pair・関数・run をまたいで集計する）。構造 key
    の tail token は発行した process の中でだけ identity になるので、それを含む key
    （`core.structural.key_is_process_independent` が偽）は解決しない
    （`process_scoped_cause_identity`）。過分割はしても、別の原因を 1 つにまとめない。
    token を作った process 自身の集計（`minting_process_identities()` の中）では解決する。
    """

    resolution = _resolve_cause_identity(
        typed_cause_key=typed_cause_key,
        object_target_key=object_target_key,
        left_binary_identity=left_binary_identity,
        right_binary_identity=right_binary_identity,
    )
    if (
        resolution.resolved
        and not _MINTING_PROCESS_SCOPE.get()
        and not key_is_process_independent(resolution.canonical_cause_key)
    ):
        return CauseIdentityResolution(diagnostic="process_scoped_cause_identity")
    return resolution


def _resolve_cause_identity(
    *,
    typed_cause_key: Any,
    object_target_key: Any,
    left_binary_identity: Tuple[Any, ...],
    right_binary_identity: Tuple[Any, ...],
) -> CauseIdentityResolution:
    # 組み込みの振る舞いの mapping だけ（`typing.Mapping` の `__subclasscheck__` は metaclass・ABC の
    # 登録表を辿る）
    if live_values.builtin_mapping(typed_cause_key) is not None:
        try:
            cause: CauseKey = cause_key_from_dict(typed_cause_key)
        except ValueError as exc:
            message = exception_text(exc, 200)
            if "unsupported typed cause schema" in message:
                diagnostic = "unknown_typed_cause_schema"
            elif "unsupported identity scope" in message:
                diagnostic = "unsupported_identity_scope"
            else:
                diagnostic = "incomplete_typed_cause_key"
            return CauseIdentityResolution(diagnostic=diagnostic)
        return CauseIdentityResolution(
            identity_scope=as_str(attribute(cause, "identity_scope")),
            cause_kind=as_str(attribute(cause, "cause_kind")),
            canonical_cause_key=freeze_identity(canonical_cause_tuple(cause)),
            typed=True,
        )
    if not as_bool(object_target_key):
        return CauseIdentityResolution()
    legacy = identity_tuple(object_target_key)
    discriminator = builtin_str(legacy[0]) if legacy else ""
    spec = LEGACY_CAUSE_SCOPES.get(discriminator)
    if spec is None:
        return CauseIdentityResolution(diagnostic="legacy_adapter_missing")
    scope, schema = spec
    validation = validate_legacy_cause_key(schema, legacy)
    if validation == "schema_invalid":
        return CauseIdentityResolution(diagnostic="legacy_cause_schema_invalid")
    if validation == "identity_incomplete":
        return CauseIdentityResolution(diagnostic="legacy_cause_identity_incomplete")
    canonical = (
        "legacy_known_canonical",
        canonicalize_legacy_cause_key(
            schema,
            legacy,
            left_binary_identity=left_binary_identity,
            right_binary_identity=right_binary_identity,
        ),
    )
    return CauseIdentityResolution(
        identity_scope=scope,
        cause_kind=discriminator,
        canonical_cause_key=canonical,
        typed=False,
    )


def canonicalize_legacy_cause_key(
    schema: str,
    key: Tuple[Any, ...],
    *,
    left_binary_identity: Tuple[Any, ...],
    right_binary_identity: Tuple[Any, ...],
) -> Tuple[Any, ...]:
    if schema == "return_coverage_v3":
        # key[2] は今回の比較における表示側でしかない。
        return freeze_identity(
            (
                key[0],
                (
                    "local_binary_content",
                    _local_binary_identity(key[2], left_binary_identity, right_binary_identity),
                ),
                key[1],
                *key[3:],
            )
        )
    if schema == "call_evidence_v1":
        # key[1] は function1/function2。function_ref と pcode identity は残す。
        return freeze_identity(
            (
                key[0],
                (
                    "local_binary_content",
                    _local_binary_identity(key[1], left_binary_identity, right_binary_identity),
                ),
                *key[2:],
            )
        )
    return freeze_identity(key)


def _local_binary_identity(
    side: str,
    left_binary_identity: Tuple[Any, ...],
    right_binary_identity: Tuple[Any, ...],
) -> Tuple[Any, ...]:
    if side == "function1":
        return left_binary_identity
    if side == "function2":
        return right_binary_identity
    raise ValueError(f"unsupported unary cause side: {side}")


def validate_legacy_cause_key(schema: str, key: Tuple[Any, ...]) -> str:
    if schema == "return_coverage_v3":
        if len(key) < 8 or key[0] != "return_coverage":
            return "schema_invalid"
        if key[1] != ("target_schema_version", 3):
            return "schema_invalid"
        if key[2] not in {"function1", "function2"}:
            return "identity_incomplete"
        required_tags = ("function_identity", "return_partition_identity", "guard_disjunction_identity")
        if not all(
            isinstance(value, tuple) and value and value[0] == tag
            for value, tag in ((key[3], required_tags[0]), (key[6], required_tags[1]), (key[7], required_tags[2]))
        ):
            return "identity_incomplete"
        if not contains_tagged_identity(key[3], "binary_identity"):
            return "identity_incomplete"
        return "valid"
    if schema == "return_width_v1":
        if len(key) != 5 or key[0] != "return_width_bridge":
            return "schema_invalid"
        if not (isinstance(key[1], tuple) and key[1][:1] == ("pair",) and key[1][1]):
            return "identity_incomplete"
        widths = key[2]
        if not (
            isinstance(widths, tuple)
            and len(widths) == 3
            and widths[0] == "return_widths"
            and all(isinstance(value, int) and value > 0 for value in widths[1:])
        ):
            return "identity_incomplete"
        if not all(isinstance(value, tuple) and len(value) >= 3 for value in key[3:]):
            return "identity_incomplete"
        return "valid"
    if schema == "solver_timeout_v1":
        if len(key) != 8 or key[0] != "solver_timeout":
            return "schema_invalid"
        required = {
            "pair": key[1],
            "stage": key[2],
            "query_hash": key[3],
            "timeout_budget_seconds": key[4],
            "solver_options": key[5],
        }
        if any(not isinstance(value, tuple) or not value for value in required.values()):
            return "schema_invalid"
        if any(value[0] != tag for tag, value in required.items()):
            return "schema_invalid"
        if not key[3][1] or not key[4][1] or not key[5][1:]:
            return "identity_incomplete"
        if not all(isinstance(value, tuple) and len(value) >= 2 for value in key[6:]):
            return "identity_incomplete"
        return "valid"
    if schema == "call_evidence_v1":
        if len(key) < 5 or key[0] not in {
            "call_argument_evidence",
            "call_target_resolution_evidence",
        }:
            return "schema_invalid"
        if key[1] not in {"function1", "function2"}:
            return "identity_incomplete"
        if not all(isinstance(value, tuple) and value for value in key[2:5]):
            return "identity_incomplete"
        if key[2][0] != "function_ref" or key[3][0] != "pcode_op":
            return "identity_incomplete"
        return "valid"
    if schema == "deferred_call_v1":
        if len(key) < 4 or key[0] != "deferred_call_site":
            return "schema_invalid"
        if not all(isinstance(value, tuple) and value for value in key[1:4]):
            return "identity_incomplete"
        return "valid"
    return "schema_invalid"


def contains_tagged_identity(value: Any, tag: str) -> bool:
    """`value`（`freeze_identity` の写し）の中に先頭が `tag` の tuple があるか（再帰しない）。"""

    pending = [value]
    while pending:
        item = pending.pop()
        if isinstance(item, tuple):
            if item and item[0] == tag:
                return True
            pending.extend(item)
    return False


def _requirement_key(requirement: Any) -> Tuple[Any, ...]:
    """proof requirement の payload の key（`ProofRequirementId.from_dict(...).to_key()`）。"""

    requirement_id = ProofRequirementId.from_dict(requirement)
    if type(requirement_id) is not ProofRequirementId:
        raise TypeError("proof requirement is not a ProofRequirementId")
    # target は構造 key を持ち得る: 別 process の結果と比べる key なので、owner の昇格規則を
    # 通す `freeze_identity` の写しにする（Issue #215 Gate A）
    return freeze_identity(requirement_id.to_key())


@dataclass(frozen=True)
class RequiredProofResolution:
    keys: Tuple[Tuple[Any, ...], ...] = ()
    complete: bool = True
    diagnostics: Tuple[str, ...] = ()


def identity_is_unmatchable_here(key: Any) -> bool:
    """`freeze_identity` の写し `key` が、今の scope では別の値と照合できない（過分割される）か。

    token を作った process の外（既定）では、構造 key の token は識別不能 token に置き換わって
    いて、同じ命題を表す別の写しとも一致しない（Issue #215 Gate A）。その key を数えた集計は
    「完全」と名乗れないので、呼び出し側は完全性の印を落とす（件数は過大にしか動かない）。
    token を作った process の中でも、識別不能 token（C-K5）を含む key は自分の写しとも一致しない。
    """

    if key_is_process_independent(key):
        return False
    return not _MINTING_PROCESS_SCOPE.get() or key_contains_unidentified(key)


def resolve_required_proofs(
    *,
    proof_requirement_ids: Sequence[Any],
    object_target_key: Any,
    identity_scope: str,
    canonical_cause_key: Tuple[Any, ...],
    recovery_actions: Sequence[Any],
) -> RequiredProofResolution:
    """reason record 1 件が要求する proof requirement key を決める（純粋関数）。

    明示 requirement が無く `object_target_key` だけがある旧 artifact は、
    recovery action から保守的に requirement を作る（reason_id と観測 stage は
    意図的に入れないので、同じ命題が reason を跨いで畳まれる）。
    """

    keys: List[Tuple[Any, ...]] = []
    complete = True
    diagnostics: List[str] = []
    explicit = tuple(_elements(proof_requirement_ids))
    for requirement in explicit:
        try:
            keys.append(_requirement_key(requirement))
        except (TypeError, ValueError) as exc:
            complete = False
            message = exception_text(exc, 200)
            if "unsupported proof requirement schema" in message:
                diagnostics.append("unknown_proof_requirement_schema")
            elif "requires kind, target, and contract" in message:
                diagnostics.append("proof_requirement_identity_incomplete")
            else:
                diagnostics.append("invalid_proof_requirement")
    if not explicit and as_bool(object_target_key):
        for action in elements_of(recovery_actions):
            proof_kind = builtin_str(attribute(action, "proof_kind", "none"))
            if proof_kind == "none":
                continue
            contract = (
                "legacy_recovery_contract",
                proof_kind,
                freeze_identity(_or(attribute(action, "required_evidence", ()), ())),
            )
            try:
                requirement = ProofRequirementId.create(
                    proof_kind,
                    ("legacy_scope_aware_target", identity_scope, canonical_cause_key),
                    contract,
                )
            except ValueError:
                continue
            keys.append(freeze_identity(requirement.to_key()))
    if any(identity_is_unmatchable_here(key) for key in keys):
        complete = False
        diagnostics.append("process_scoped_proof_requirement")
    return RequiredProofResolution(tuple(keys), complete, tuple(diagnostics))


# ---------------------------------------------------------------------------
# 因果（completion / transition）の解決（reporting と共有）
# ---------------------------------------------------------------------------

def attempt_ordinal(value: Any) -> Optional[int]:
    if builtin_mapping(value) is None:
        return None
    raw = lookup(value, "attempt_ordinal")
    try:
        return as_int(raw)
    except (TypeError, ValueError):
        return None


def cyclic_nodes(edges: Mapping[Any, Any]) -> set:
    """`edges`（node → 次の node、1 本ずつ）の閉路に載る node。

    Issue #22 PR-22-D: 辿り終えた node を覚えて、各 node を 1 回だけ辿る（辺の数に比例）。
    始点ごとに鎖を辿り直さない（長い鎖で辺の数の 2 乗にならない）。
    """

    cyclic = set()
    finished = set()
    for start in edges:
        if start in finished:
            continue
        path: List[Any] = []
        positions: Dict[Any, int] = {}
        current = start
        while current in edges and current not in finished:
            if current in positions:
                cyclic.update(path[positions[current]:])
                break
            positions[current] = len(path)
            path.append(current)
            current = edges[current]
        finished.update(path)
    return cyclic


def resolve_occurrence_transitions(
    occurrences: Sequence[Mapping[str, Any]],
    transitions: Sequence[Any],
    completions: Sequence[Any],
    diagnostics: Optional[Dict[str, int]],
    *,
    reason_completions: Sequence[Any] = (),
) -> Dict[Any, str]:
    """occurrence_id -> 実効 causal status。完了/遷移の証拠だけで決める。"""

    occurrence_by_id = {
        freeze_identity(lookup(item, "occurrence_id")): item for item in occurrences
    }
    # key は `freeze_identity` の写し（組み込みの値）: key の集合は同じ写しから作る
    occurrence_ids = {freeze_identity(lookup(item, "occurrence_id")) for item in occurrences}
    result: Dict[Any, str] = {}
    for completion in reason_completions:
        if builtin_mapping(completion) is None:
            continue
        target = freeze_identity(lookup(completion, "completed_occurrence_id"))
        if builtin_str(lookup(completion, "applicability_status")) != "APPLICABLE":
            _bump(diagnostics, "inapplicable_reason_completion")
            continue
        if target not in occurrence_ids:
            _bump(diagnostics, "dangling_reason_completion_target")
            continue
        record = _or(lookup(occurrence_by_id[target], "reason_record"), {})
        expected_target = freeze_identity(lookup(record, "object_target_key"))
        observed_target = freeze_identity(lookup(completion, "exact_target_id"))
        expected_slots = {
            builtin_str(_or(lookup(item, "proof_kind"), ""))
            for item in _elements(lookup(record, "proof_requirement_ids"))
            if builtin_mapping(item) is not None
        }
        observed_slot = builtin_str(_or(lookup(completion, "exact_missing_fact_or_proof_slot"), ""))
        if (
            (expected_target and expected_target != observed_target)
            or (expected_slots and observed_slot not in expected_slots)
            or not as_bool(lookup(completion, "source_snapshot_fingerprint"))
            or not as_bool(lookup(completion, "semantic_seed_or_premise_digest"))
            or not as_bool(lookup(completion, "evidence_or_artifact_digest"))
            or not as_bool(lookup(completion, "recognizing_stage"))
        ):
            _bump(diagnostics, "invalid_reason_completion_applicability")
            continue
        completed_ordinal = attempt_ordinal(lookup(completion, "completed_at_attempt"))
        target_ordinal = attempt_ordinal(lookup(occurrence_by_id[target], "attempt_identity"))
        if (
            completed_ordinal is None
            or target_ordinal is None
            or completed_ordinal <= target_ordinal
        ):
            _bump(diagnostics, "non_forward_reason_completion")
            continue
        result[target] = "discharged"
    seen = set()
    by_target: Dict[Any, set] = {}
    # 並びは各 transition の写しの `repr`（transition 自身は比べない）
    transitions = list(transitions)
    ordered_transitions = _in_key_order(
        transitions, [repr(freeze_identity(item)) for item in transitions],
    )
    for transition in ordered_transitions:
        if builtin_mapping(transition) is None:
            continue
        transition_id = freeze_identity(lookup(transition, "transition_id"))
        if transition_id in seen:
            continue
        seen.add(transition_id)
        target = freeze_identity(lookup(transition, "target_occurrence_id"))
        if target not in occurrence_ids:
            _bump(diagnostics, "dangling_transition_target")
            continue
        kind = builtin_str(_or(lookup(transition, "transition_kind"), ""))
        cause_kind = builtin_str(_or(lookup(transition, "cause_kind"), ""))
        cause_ref = freeze_identity(lookup(transition, "cause_ref"))
        valid = False
        emitted_ordinal = attempt_ordinal(lookup(transition, "emitted_at_attempt"))
        target_ordinal = attempt_ordinal(lookup(occurrence_by_id[target], "attempt_identity"))
        if emitted_ordinal is None or target_ordinal is None or emitted_ordinal <= target_ordinal:
            _bump(diagnostics, "non_forward_causal_transition")
            continue
        if kind == "superseded" and cause_kind == "reason_occurrence":
            valid = cause_ref in occurrence_ids
        if not valid:
            _bump(diagnostics, "dangling_transition_cause")
            continue
        by_target.setdefault(target, set()).add((kind, cause_kind, cause_ref))
    for target, values in by_target.items():
        if len(values) != 1:
            _bump(diagnostics, "conflicting_causal_transitions")
            continue
        kind = next(iter(values))[0]
        prior = result.get(target)
        if prior is not None and prior != kind:
            _bump(diagnostics, "conflicting_causal_transitions")
            result.pop(target, None)
            continue
        result[target] = kind
    supersession_edges = {
        target: next(iter(values))[2]
        for target, values in by_target.items()
        if len(values) == 1 and next(iter(values))[0] == "superseded"
    }
    cyclic = cyclic_nodes(supersession_edges)
    for target in cyclic:
        result.pop(target, None)
    if cyclic and diagnostics is not None:
        diagnostics["causal_transition_cycle"] = len(cyclic)
    return result


def _bump(diagnostics: Optional[Dict[str, int]], key: str, amount: int = 1) -> None:
    if diagnostics is None:
        return
    diagnostics[key] = int(diagnostics.get(key, 0) or 0) + amount


def _truthy(value: Any) -> bool:
    """`bool(value)`（`live_values.as_bool`。`None` は偽）。"""

    return value is not None and as_bool(value)


def _or(value: Any, default: Any) -> Any:
    """`value or default`（真偽は `live_values.as_bool` で決める。live な値の `__bool__` を呼ばない）。"""

    if value is None:
        return default
    return value if as_bool(value) else default


def _elements(value: Any):
    """`value or ()` の要素（組み込みの振る舞いの列・集合・iterator だけを辿る。無い値は空）。

    `None` と偽の scalar（`0` / `""` / `False`）は空。それ以外は `live_values.elements_of`
    （辿れない値は `TypeError`: 集計は `error` を持つ値になる）。
    """

    if value is None:
        return iter(())
    base = plain_scalar(value)
    if base is not _NOT_PLAIN_SCALAR and not base:
        return iter(())
    return elements_of(value)


# ---------------------------------------------------------------------------
# reason record の集計（reporting と共有）
# ---------------------------------------------------------------------------

def select_primary_reason_records(
    records: Iterable[UnknownReasonRecord],
) -> Tuple[UnknownReasonRecord, ...]:
    """集計単位ごとに 1 件だけ残す（validation UNKNOWN unit の定義）。

    `checker.unknown_reason._select_primary_records_by_aggregation_unit` は
    「最初に来た record」を残すが、こちらは decision_effect の優先順で決める。
    別々の契約なので統合しない。
    """

    grouped: Dict[Tuple[str, Any], List[UnknownReasonRecord]] = {}
    fallback_index = 0
    for record in records:
        aggregation_key = builtin_str(_or(attribute(record, "aggregation_unit"), "result"))
        unit_key = _or(attribute(record, "pair_or_case"), attribute(record, "stage"))
        if unit_key is None:
            unit_key = f"record:{fallback_index}"
            fallback_index += 1
        # `pair_or_case` は 2 要素の case 対のこともあり、JSON 往復後は list に
        # なる。hash 可能な frozen 表現へ正規化してから集計単位のキーにする。
        grouped.setdefault((aggregation_key, freeze_identity(unit_key)), []).append(record)
    return tuple(
        min(group, key=primary_reason_record_sort_key) for group in grouped.values()
    )


def primary_reason_record_sort_key(record: UnknownReasonRecord) -> Tuple[Any, ...]:
    return (
        PRIMARY_DECISION_EFFECT_PRIORITY.get(builtin_str(attribute(record, "decision_effect")), 99),
        builtin_str(attribute(record, "reason_id")),
        builtin_str(attribute(record, "reason_scope")),
        builtin_str(attribute(record, "recovery_proof_kind")),
        builtin_str(_or(attribute(record, "proof_stage"), "")),
        builtin_str(_or(attribute(record, "action_status"), "")),
        tuple(builtin_str(ref) for ref in _elements(attribute(record, "evidence_refs"))),
        builtin_str(_or(attribute(record, "detail"), "")),
    )


def is_proof_backlog(record: UnknownReasonRecord, actions: Sequence[Any] = ()) -> bool:
    action_statuses = {builtin_str(attribute(action, "status", "")) for action in elements_of(actions)}
    # 文字列の値で比べる（`json_scalar`: 文字列と文字列の enum は基底型の `str`。live な値の
    # `__hash__` / `__eq__` を呼ばない）
    return (
        json_scalar(attribute(record, "reason_class")) in PROOF_BACKLOG_CLASSES
        or json_scalar(attribute(record, "action_status"))
        in {
            UnknownRecoveryActionStatus.PENDING_PROOF.value,
            UnknownRecoveryActionStatus.PLANNED.value,
        }
        or (
            attribute(record, "object_target_key") is not None
            and bool(
                action_statuses
                & {
                    UnknownRecoveryActionStatus.PENDING_PROOF.value,
                    UnknownRecoveryActionStatus.PLANNED.value,
                }
            )
        )
    )


def global_reason_tuple_from_record(
    record: UnknownReasonRecord,
    count_kind: str,
) -> Tuple[str, ...]:
    return (
        builtin_str(count_kind),
        builtin_str(attribute(record, "reason_id")),
        builtin_str(attribute(record, "decision_effect")),
        builtin_str(attribute(record, "reason_scope")),
        builtin_str(_or(attribute(record, "recovery_proof_kind"), UNKNOWN_TUPLE_MISSING)),
        builtin_str(_or(attribute(record, "proof_stage"), UNKNOWN_TUPLE_MISSING)),
        builtin_str(_or(attribute(record, "action_status"), UNKNOWN_TUPLE_MISSING)),
    )


def global_reason_tuple_from_action(action: Any) -> Tuple[str, ...]:
    return (
        builtin_str(attribute(action, "count_kind", UnknownCountKind.PROOF_ACTION.value)),
        builtin_str(attribute(action, "reason_id", UnknownReasonId.UNKNOWN.value)),
        builtin_str(attribute(action, "decision_effect", UNKNOWN_TUPLE_MISSING)),
        builtin_str(attribute(action, "reason_scope", UNKNOWN_TUPLE_MISSING)),
        builtin_str(attribute(action, "proof_kind", UNKNOWN_TUPLE_MISSING)),
        builtin_str(attribute(action, "proof_stage", UNKNOWN_TUPLE_MISSING)),
        builtin_str(attribute(action, "status", UNKNOWN_TUPLE_MISSING)),
    )


def recovery_action_key(action: Any) -> str:
    return " | ".join(
        builtin_str(value)
        for value in (
            attribute(action, "reason_id", "unknown"),
            attribute(action, "proof_kind", "none"),
            attribute(action, "proof_stage", "unspecified"),
            attribute(action, "status", "unspecified"),
        )
    )


def reason_detail_key(record: Any) -> str:
    """`reason_id | detail` 集計キー（detail 無しは明示する）。

    Issue #22 PR-22-D: detail は出力の行 schema と同じ文字数まで（超えた分は marker）。
    出力の reason 行から読む reporting と、live な record から作る集計で同じ key になる。
    """
    from scripts.function_tracer_pcode.checker.unknown_reason import DETAIL_MAX_CHARS
    from scripts.function_tracer_pcode.core.budget_policy import active_serialization_work
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget, bounded_text

    # 長い detail の marker の hash は今の直列化の作業量の中で求める（scope の外 = 部品単体の
    # 呼び出しでは数えない）
    work = active_serialization_work() or JsonBudget(None)
    detail = bounded_text(attribute(record, "detail"), DETAIL_MAX_CHARS, work=work)
    reason_id = builtin_str(attribute(record, "reason_id"))
    return f"{reason_id} | {detail if detail else '(no detail)'}"


def build_reason_view(records: Sequence[UnknownReasonRecord]) -> Dict[str, Any]:
    """record 集合 1 つ分の集計。`summarize_validation_unknowns` と同じ次元。

    空の record 集合でも「0 件」として view を返す。view を作るかどうか
    （= その源の証拠があるか）は呼び出し側が決める。reporting 側の
    「record が 1 件も無い結果」の合成は結果単位の話なのでここではしない。
    """

    records = tuple(elements_of(records))
    primary = select_primary_reason_records(records)
    by_reason: Dict[str, int] = {}
    by_decision_effect: Dict[str, int] = {}
    by_reason_scope: Dict[str, int] = {}
    by_reason_detail: Dict[str, int] = {}
    validation_multiset: Dict[Tuple[str, ...], int] = {}
    record_multiset: Dict[Tuple[str, ...], int] = {}
    action_multiset: Dict[Tuple[str, ...], int] = {}
    backlog_by_reason: Dict[str, int] = {}
    backlog_by_proof_kind: Dict[str, int] = {}
    backlog_by_recovery_action: Dict[str, int] = {}
    backlog_by_action_status: Dict[str, int] = {}
    operational_by_reason: Dict[str, int] = {}
    operational_by_class: Dict[str, int] = {}

    for record in records:
        _inc_row(record_multiset, global_reason_tuple_from_record(
            record, UnknownCountKind.REASON_RECORD.value
        ))
        for action in elements_of(build_unknown_recovery_actions((record,), work=_diagnostic_work())):
            _inc_row(action_multiset, global_reason_tuple_from_action(action))

    for record in primary:
        _inc(by_reason_detail, reason_detail_key(record))
        _inc_row(validation_multiset, global_reason_tuple_from_record(
            record, UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value
        ))
        _inc(by_reason, attribute(record, "reason_id"))
        _inc(by_decision_effect, attribute(record, "decision_effect"))
        _inc(by_reason_scope, attribute(record, "reason_scope"))
        actions = tuple(elements_of(build_unknown_recovery_actions((record,), work=_diagnostic_work())))
        if is_proof_backlog(record, actions):
            _inc(backlog_by_reason, attribute(record, "reason_id"))
            for action in actions:
                _inc(backlog_by_proof_kind, attribute(action, "proof_kind"))
                _inc(backlog_by_recovery_action, recovery_action_key(action))
                _inc(backlog_by_action_status, attribute(action, "status"))
        else:
            _inc(operational_by_reason, attribute(record, "reason_id"))
            _inc(operational_by_class, attribute(record, "reason_class"))

    return {
        "unit_count": size(primary),
        "record_count": size(records),
        "by_reason": by_reason,
        "by_decision_effect": by_decision_effect,
        "by_reason_scope": by_reason_scope,
        "by_reason_detail": by_reason_detail,
        "validation_unknown_unit_multiset": _multiset_rows(validation_multiset),
        "reason_record_multiset": _multiset_rows(record_multiset),
        "proof_action_multiset": _multiset_rows(action_multiset),
        "backlog": {
            "by_reason": backlog_by_reason,
            "by_proof_kind": backlog_by_proof_kind,
            "by_recovery_action": backlog_by_recovery_action,
            "by_action_status": backlog_by_action_status,
        },
        "operational": {
            "by_reason": operational_by_reason,
            "by_class": operational_by_class,
        },
    }


def _multiset_rows(counts: Mapping[Tuple[str, ...], int]) -> List[Dict[str, Any]]:
    """tuple キーの multiset を JSON 可能な行へ（区切り文字で潰さない）。"""
    return [
        {"key": list(key), "count": int(value)}
        for key, value in sorted(counts.items(), key=_multiset_row_order)
    ]


def _multiset_row_order(item: Tuple[Tuple[str, ...], int]) -> Tuple[str, ...]:
    return tuple(builtin_str(part) for part in item[0])


def multiset_from_rows(rows: Any) -> Dict[Tuple[str, ...], int]:
    """`_multiset_rows` の逆。読み取り側（reporting）が使う。"""
    counts: Dict[Tuple[str, ...], int] = {}
    for row in rows or ():
        if not isinstance(row, Mapping):
            continue
        key = tuple(builtin_str(part) for part in (row.get("key") or ()))
        counts[key] = counts.get(key, 0) + int(row.get("count") or 0)
    return counts


def _inc(counts: Dict[Any, int], key: Any, amount: int = 1) -> None:
    """文字列の key（`builtin_str` の写し）の件数を足す。"""
    count_key = builtin_str(key)
    counts[count_key] = int(counts.get(count_key, 0) or 0) + int(amount)


def _inc_row(counts: Dict[Tuple[str, ...], int], key: Tuple[str, ...], amount: int = 1) -> None:
    """multiset の行（`global_reason_tuple_*` が作る文字列の tuple）の件数を足す。"""
    counts[key] = int(counts.get(key, 0) or 0) + int(amount)


# ---------------------------------------------------------------------------
# aggregate の生成
# ---------------------------------------------------------------------------

def attach_cause_aggregate(result: Any) -> None:
    """canonical bundle を組む前に aggregate を確定して結果へ載せる。

    `to_dict()` は field が無ければ自分で組むので、この呼び出しは「preimage を
    作る前に一度だけ確定させる」ためのもの。preimage 確定後に payload を
    書き換えてはならない（`checker/diagnostics.py` の digest 契約と同じ）。
    """
    from scripts.function_tracer_pcode.checker.result import EquivalenceResult
    from scripts.function_tracer_pcode.core.budget_policy import serialization_scope

    # Issue #22 PR-22-D: 集計が読む値（canonical reason・準備済みの trace 部分）は、authority
    # 確定後の field に空けた headroom を上限にした診断用の作業量へ数えながら読む（超えれば
    # `error` を持つ値 = 診断の marker。判定は変えない）
    prepared = attribute(result, "prepared_semantic_payload")
    plan = attribute(prepared, "plan") if prepared is not None else None
    limit = None
    if plan is not None and attribute(plan, "max_bytes") is not None:
        headroom = attribute(plan, "headroom_bytes")
        limit = as_int(headroom) if headroom is not None else None
    try:
        with serialization_scope(
            site=AGGREGATE_SITE, target_parts=("unknown_cause_aggregate",),
            terminal=False, max_bytes=limit, enabled=limit is not None,
        ):
            aggregate = build_unknown_cause_aggregate(result)
            # 載せる先は package の結果の型だけ（その型の `__setattr__` だけが走る）。それ以外の
            # object には載せない（`to_dict()` 相当の出力はその場で集計を組む）
            if type(result) is EquivalenceResult:
                live_values.set_state(result, "unknown_cause_aggregate", aggregate)
    except Exception:  # 診断は判定を壊さない
        return


def build_unknown_cause_aggregate(
    result: Any,
    *,
    trace_evidence_for: Optional[Tuple[Any, Any]] = None,
) -> Optional[Dict[str, Any]]:
    """`debug_trace` を省いても原因分析を失わない compact な集計を作る。

    full trace の複製ではない: record 本体・solver 行・SMT・counterexample は
    持たず、reporting が読む集計と identity だけを持つ。

    `trace_evidence_for=(binary1, binary2)` を渡すと、authority 確定 **前** に作る
    trace 由来の部分（`build_trace_cause_evidence`）だけを作る。どちらも診断なので、
    失敗しても判定を壊さず `error` を持つ値を返す（同じ fail-open の規則）。
    """
    if result is None:
        return None
    try:
        # 集計するのは今の process が作った結果（token はこの process の identity）
        with minting_process_identities():
            if trace_evidence_for is not None:
                return build_trace_cause_evidence(result, binary_identities=trace_evidence_for)
            return _build_unknown_cause_aggregate(result)
    except Exception as exc:  # 診断は判定を壊さない
        return {
            "schema": (
                TRACE_CAUSE_EVIDENCE_SCHEMA if trace_evidence_for is not None
                else UNKNOWN_CAUSE_AGGREGATE_SCHEMA
            ),
            "error": exception_text(exc, 200),
        }


def aggregate_is_usable(aggregate: Any) -> bool:
    """reporting が集計源として使ってよい aggregate か（3 段 fallback の第 1 段）。"""
    return (
        isinstance(aggregate, Mapping)
        and aggregate.get("schema") == UNKNOWN_CAUSE_AGGREGATE_SCHEMA
        and not aggregate.get("error")
    )


#: authority 確定前（G4-b）に作る、trace 由来の部分の schema。
TRACE_CAUSE_EVIDENCE_SCHEMA = "unknown-cause-trace-evidence-v1"


def build_trace_cause_evidence(
    result: Any,
    *,
    binary_identities: Tuple[Any, Any] = (None, None),
) -> Dict[str, Any]:
    """aggregate のうち **trace だけで決まる部分**（Issue #22 PR-22-D）。

    authority 確定 **前**（G4-b、`checker/output_preparation.prepare_pair_output`）に
    live な trace から 1 回だけ作り、有界な canonical JSON として準備する。authority
    確定後の aggregate（`build_unknown_cause_aggregate`）はこの準備済みの値と canonical
    reason だけを読み、live な trace を読み直さない。

    trace に occurrence が無い結果は、root cause を canonical reason から作る
    （authority 後）ので、ここでは trace の event だけを残す。
    """

    trace = attribute(result, "debug_trace")
    # 集計は trace の列を直接読むので、読む要素の大きさを 1 つずつ作業量へ数えてから読む
    # （集計の作業は数えた入力で抑えられる）。trace の field は `live_values.attribute` だけで読む
    attempts = tuple(_counted(attribute(trace, "attempts", ()), mode=LEGACY)) if trace is not None else ()
    occurrences = _trace_occurrence_views(attempts)
    transitions = _event_views(_counted(
        attribute(trace, "causal_transitions", ()) if trace is not None else (), mode=LEGACY,
    ))
    completions = _event_views(_counted(
        attribute(trace, "proof_completion_events", ()) if trace is not None else (), mode=LEGACY,
    ))
    reason_completions = _event_views(_counted(
        attribute(trace, "reason_completion_events", ()) if trace is not None else (), mode=LEGACY,
    ))
    legacy_attempt, legacy_records = _final_legacy_attempt(trace, attempts)
    legacy_view = None
    if trace is not None and legacy_attempt is not None:
        # 最終 attempt の record は attempt と一緒に数え済み
        legacy_view = build_reason_view(legacy_records)
        legacy_view["source"] = "final_attempt"
    evidence: Dict[str, Any] = {
        "schema": TRACE_CAUSE_EVIDENCE_SCHEMA,
        "trace_present": trace is not None,
        "has_final_attempt": legacy_attempt is not None,
        "has_trace_occurrences": size(occurrences) > 0,
        "legacy_view": legacy_view,
        "attempts": _attempt_summary(attempts, legacy_attempt) if trace is not None else None,
    }
    if size(occurrences) > 0:
        diagnostics: Dict[str, int] = {}
        root_causes, root_cause_stats, identity_pool = _build_root_causes(
            binary_identities,
            occurrences=occurrences,
            transitions=transitions,
            completions=completions,
            reason_completions=reason_completions,
            attempts=attempts,
            diagnostics=diagnostics,
        )
        evidence["root_causes"] = root_causes
        evidence["root_cause_stats"] = root_cause_stats
        evidence["identity_pool"] = identity_pool
        evidence["completions"] = (
            completion_counts(completions, reason_completions, occurrences)
            if trace is not None else None
        )
        evidence["transitions"] = (
            transition_counts(transitions, occurrences) if trace is not None else None
        )
    else:
        # root cause は authority 後に canonical reason から作る（trace の event だけ残す）
        evidence["transition_events"] = transitions
        evidence["completion_events"] = completions
        evidence["reason_completion_events"] = reason_completions
        evidence["final_attempt_identity"] = _final_attempt_identity(attempts, ())
    return evidence


#: authority 確定後に集計を作る観測点（診断用の作業量）。
AGGREGATE_SITE = "checker.cause_aggregate.attach"


def _counted(values: Any, *, mode: str):
    """集計が読む列を、1 要素ずつ今の直列化の作業量へ数えてから渡す（入力を先に写さない）。

    * authority 確定 **前** の trace（live な記録）は `LEGACY`（集計が読む形そのもの）で数える。
    * authority 確定 **後** の canonical reason は `CANONICAL`（出力と同じ有界な行: 封印済みの
      key は `cause:<id>` の要約で、辿らない）で数える。

    作業量（`serialization_scope` の診断用の work）を超えれば、そこで
    `JsonBudgetExhausted` が上がり、集計は `error` を持つ値になる（fail open）。作業量の
    scope の外（部品単体の呼び出し）では数えない。
    """

    from scripts.function_tracer_pcode.core.budget_policy import active_serialization_work

    work = active_serialization_work()
    for value in _elements(values):
        if work is not None:
            json_encoding.RESULT_JSON_POLICY.count_into(value, work, mode=mode)
        yield value


def trace_evidence_is_usable(evidence: Any) -> bool:
    return (
        builtin_mapping(evidence) is not None
        and json_scalar(lookup(evidence, "schema")) == TRACE_CAUSE_EVIDENCE_SCHEMA
        and not as_bool(lookup(evidence, "error"))
    )


def _build_unknown_cause_aggregate(result: Any) -> Dict[str, Any]:
    evidence = _prepared_trace_evidence(result)
    if evidence is None:
        # pair 境界を通らずに組んだ結果（test の直接構築など）: その場で作る
        evidence = build_trace_cause_evidence(
            result,
            binary_identities=(
                attribute(result, "binary1_content_identity"),
                attribute(result, "binary2_content_identity"),
            ),
        )
    if not trace_evidence_is_usable(evidence):
        detail = None
        if builtin_mapping(evidence) is not None:
            detail = _or(lookup(evidence, "error"), lookup(evidence, "reason"))
        return {
            "schema": UNKNOWN_CAUSE_AGGREGATE_SCHEMA,
            "error": ("trace_evidence_unavailable: " + builtin_str(detail))[:200],
        }
    # evidence は package が組んだ dict か、authority 前に準備した canonical な値（どちらも
    # `lookup` で読む）
    trace_present = as_bool(lookup(evidence, "trace_present"))

    canonical_records = coerce_unknown_reason_records(
        _counted(attribute(result, "unknown_reasons", ()), mode=CANONICAL)
    )
    canonical_available = attribute(result, "decision_receipt") is not None

    final_reasons = build_reason_view(canonical_records) if canonical_available else None
    # `legacy_view` は「trace を見た consumer が診断に使う record 集合」の集計で、
    # **trace を観測できたときだけ**作る。trace がもともと無い結果では `null` に
    # して、「観測できなかった」と「観測して 0 件」を取り違えさせない。
    # `source` はどちらの record 集合を選んだかで、consumer の選択規則と一致する:
    #   final_attempt   -- 最終 UNKNOWN/TIMEOUT attempt の record（0 件もあり得る）
    #   payload_records -- 最終 attempt が無いので結果の `unknown_reasons`
    legacy_view = None
    if trace_present:
        if as_bool(lookup(evidence, "has_final_attempt")):
            legacy_view = lookup(evidence, "legacy_view")
        else:
            legacy_view = build_reason_view(canonical_records)
            legacy_view["source"] = "payload_records"
    effective_view = final_reasons if final_reasons is not None else legacy_view
    effective_source = (
        "canonical" if final_reasons is not None
        else ("legacy" if legacy_view is not None else None)
    )

    if as_bool(lookup(evidence, "has_trace_occurrences")):
        root_causes = lookup(evidence, "root_causes")
        root_cause_stats = lookup(evidence, "root_cause_stats")
        identity_pool = lookup(evidence, "identity_pool")
        completions_block = lookup(evidence, "completions")
        transitions_block = lookup(evidence, "transitions")
    else:
        # trace に occurrence が無い: root cause は canonical reason（authority の出力）から
        occurrences = _payload_occurrence_views(canonical_records)
        transitions = list(_elements(lookup(evidence, "transition_events")))
        completions = list(_elements(lookup(evidence, "completion_events")))
        reason_completions = list(_elements(lookup(evidence, "reason_completion_events")))
        diagnostics: Dict[str, int] = {}
        root_causes, root_cause_stats, identity_pool = _build_root_causes(
            (
                attribute(result, "binary1_content_identity"),
                attribute(result, "binary2_content_identity"),
            ),
            occurrences=occurrences,
            transitions=transitions,
            completions=completions,
            reason_completions=reason_completions,
            attempts=(),
            diagnostics=diagnostics,
            final_identity=_payload_final_identity(evidence, occurrences),
        )
        completions_block = (
            completion_counts(completions, reason_completions, occurrences)
            if trace_present else None
        )
        transitions_block = transition_counts(transitions, occurrences) if trace_present else None

    return {
        "schema": UNKNOWN_CAUSE_AGGREGATE_SCHEMA,
        "final_reasons": final_reasons,
        "legacy_view": legacy_view,
        "effective_source": effective_source,
        # view の block の写し（容器だけ作り直す。値は件数と文字列）
        "backlog": (
            copy_legacy_containers(lookup(effective_view, "backlog"))
            if effective_view is not None else None
        ),
        "operational": (
            copy_legacy_containers(lookup(effective_view, "operational"))
            if effective_view is not None else None
        ),
        "completions": completions_block,
        "transitions": transitions_block,
        "root_causes": root_causes,
        "identity_pool": identity_pool,
        "root_cause_stats": root_cause_stats,
        "attempts": lookup(evidence, "attempts") if trace_present else None,
        # `evidence_present` は「件数が非 0 か」ではなく **「その情報を観測できたか」**。
        # trace を見られなかったのか、見た上で 0 件だったのかを consumer が区別する
        # ための証言で、block の `null` と対になる。
        # 例: trace 有り・attempt 0 件 -> `attempts={"count": 0,…}` + `True`、
        #     trace 無し             -> `attempts=None`            + `False`。
        "evidence_present": {
            "debug_trace": trace_present,
            "attempts": trace_present,
            "completion_events": trace_present,
            "causal_transitions": trace_present,
            "legacy_records": trace_present,
            "canonical_reasons": canonical_available,
        },
    }


def _prepared_trace_evidence(result: Any) -> Any:
    prepared = attribute(result, "prepared_semantic_payload")
    cause_evidence = attribute(prepared, "cause_evidence") if prepared is not None else None
    # 準備済みの値（`PreparedJson`: owner の型）だけを読む
    if type(cause_evidence) is not json_encoding.PreparedJson:
        return None
    return cause_evidence.value()


def _trace_occurrence_views(attempts: Sequence[Any]) -> List[Dict[str, Any]]:
    """trace の occurrence 列（`root_blocker_summary._extract_occurrences` と同じ）。"""
    occurrences: List[Dict[str, Any]] = []
    for attempt in attempts:
        for occurrence in tuple(_elements(attribute(attempt, "reason_occurrences", ()))):
            occurrences.append(_as_mapping(occurrence))
    return occurrences


def _payload_occurrence_views(records: Sequence[UnknownReasonRecord]) -> List[Dict[str, Any]]:
    """trace に occurrence が無いときの occurrence 列（結果の reason から作る）。

    Issue #22 PR-22-D: record は出力と同じ有界な表現で読む（authority 後に大きい key を
    辿り直さない。root cause の identity は `typed_cause_key` から決まる）。
    """
    identity = {"trace_schema_version": 1, "strategy_identity": "payload", "attempt_ordinal": 0}
    occurrences: List[Dict[str, Any]] = []
    for ordinal, record in enumerate(elements_of(records)):
        occurrences.append({
            "occurrence_id": {
                "occurrence_schema_version": 1,
                "attempt_identity": identity,
                "reason_ordinal": ordinal,
            },
            "attempt_identity": identity,
            "reason_record": _prepared_within_work(record),
            "initial_causal_status": "unclassified",
        })
    return occurrences


def _prepared_within_work(record: Any) -> Any:
    """record を出力と同じ有界な行にする。

    写しは、作る走査そのものが今の直列化の作業量へ byte と作業量を数えながら作る（`prepare_into`:
    数えた量と写しの中身が食い違わない）。`_counted` が数えたのは集計が **読む** 仕事で、写しを
    **作る** 仕事はこの走査の分（別の仕事を 1 回ずつ数える）。作業量の scope の外（部品単体の
    呼び出し）では数えない。
    """

    from scripts.function_tracer_pcode.core.budget_policy import active_serialization_work

    work = active_serialization_work()
    if work is None:
        return json_encoding.RESULT_JSON_POLICY.prepare(record).value()
    return json_encoding.RESULT_JSON_POLICY.prepare_into(record, work)


def _payload_final_identity(evidence: Mapping[str, Any], occurrences: Sequence[Mapping[str, Any]]):
    identity = lookup(evidence, "final_attempt_identity")
    if identity is not None:
        return freeze_identity(identity)
    if occurrences:
        return freeze_identity(lookup(occurrences[-1], "attempt_identity"))
    return None


def _event_views(values: Iterable[Any]) -> List[Dict[str, Any]]:
    # `values` は `_counted` が作る generator（数えた要素を 1 つずつ渡す）
    return [_as_mapping(value) for value in values]


#: `make_unknown_reason` が文字列にする（`str()` を呼ぶ）field
_STRINGIFIED_REASON_FIELDS = (
    "reason_id", "recovery_proof_kind", "action_status", "evidence_kind", "count_kind",
    "reason_class", "decision_effect", "reason_scope", "aggregation_unit",
)


def _plain_reason_value(value: Any) -> Any:
    base = plain_scalar(value)
    if base is not _NOT_PLAIN_SCALAR or value is None:
        return base if value is not None else None
    if builtin_view(value)[0]:
        return value
    return builtin_str(value)


def _plain_reason_payload(record: Mapping[str, Any]) -> Dict[str, Any]:
    """record の payload を構築し直す前に、文字列にされる field を組み込みの値だけにする。

    `UnknownReasonRecord.from_dict`（`make_unknown_reason`）はこの field に `str()` を呼ぶ。trace の
    record は構築時に文字列になっているが、構築を通らずに live な値を持つ record もあり得る:
    その値は型名の印にしてから渡す（live な値の `__str__` を呼ばない）。組み込みの値は変わらない。
    """

    # `from_dict` が読むのは文字列の key だけなので、文字列の key（基底型の `str`）の項だけを写す
    # （live な key の `__hash__` / `__eq__` を呼ばない）
    payload: Dict[str, Any] = {}
    for key, item in items_of(record):
        name = live_values.str_value(key)
        if name is not live_values.NOT_PLAIN:
            payload[name] = item
    for key in _STRINGIFIED_REASON_FIELDS:
        if payload.get(key) is not None:
            payload[key] = _plain_reason_value(payload[key])
    refs = payload.get("evidence_refs")
    if refs is not None:
        plain_refs = tuple(_plain_reason_value(ref) for ref in _elements(refs))
        if plain_refs:
            payload["evidence_refs"] = plain_refs
    return payload


def _diagnostic_work() -> Any:
    """集計が作る action の作業量（診断の直列化の作業量の中なら、それ。無ければ数えない）。"""

    from scripts.function_tracer_pcode.core.budget_policy import active_serialization_work

    return active_serialization_work()


def _as_mapping(value: Any) -> Dict[str, Any]:
    # 組み込みの振る舞いの mapping と json record（`to_dict()` は `materialize` が作業量の中で
    # 作る）だけを読む。それ以外の object の `to_dict()`（任意の producer）は呼ばない
    # 組み込みの振る舞いの mapping はそのまま（集計は `lookup` で読むだけで書き換えない）。json record
    # は LEGACY の写し（旧 `to_dict()` と同じ `materialize`。record の `to_dict` は呼ばない）
    mapping = builtin_mapping(value)
    if mapping is not None:
        return mapping
    if is_json_record(value):
        # 値は `_counted` が同じ作業量へ数え済み: 数え直さない写し（数えた量と同じ大きさ）
        payload = json_encoding.RESULT_JSON_POLICY.materialize(value, counted=True)
        if type(payload) is dict:
            return payload
    return {}


def _final_legacy_attempt(trace: Any, attempts: Sequence[Any]):
    """legacy 最終 attempt（`_extract_final_unknown_reasons` の legacy 分岐と同条件）。"""
    if trace is None or attribute(trace, "final_result") is not None:
        return None, ()
    for attempt in reversed(tuple(attempts)):
        if (
            attribute(attempt, "result") is None
            and builtin_str(attribute(attempt, "transition_reason", "")) in FINAL_UNKNOWN_TRANSITIONS
        ):
            return attempt, coerce_unknown_reason_records(
                tuple(_elements(attribute(attempt, "unknown_reasons", ())))
            )
    return None, ()


def _final_attempt_identity(attempts: Sequence[Any], occurrences: Sequence[Mapping[str, Any]]):
    for attempt in reversed(tuple(attempts)):
        if (
            attribute(attempt, "result") is None
            and builtin_str(attribute(attempt, "transition_reason", "")) in FINAL_UNKNOWN_TRANSITIONS
        ):
            return freeze_identity({
                "trace_schema_version": 1,
                "strategy_identity": builtin_str(
                    _or(_or(attribute(attempt, "strategy"), attribute(attempt, "phase")), "unknown")
                ),
                "attempt_ordinal": as_int(_or(attribute(attempt, "attempt_id", 0), 0)),
            })
    if occurrences:
        return freeze_identity(lookup(occurrences[-1], "attempt_identity"))
    return None


def _attempt_summary(attempts: Sequence[Any], legacy_attempt: Any) -> Dict[str, Any]:
    final = legacy_attempt if legacy_attempt is not None else (attempts[-1] if attempts else None)
    return {
        "count": size(attempts),
        "final": None if final is None else {
            "strategy": attribute(final, "strategy"),
            "attempt_id": attribute(final, "attempt_id"),
            "transition_reason": attribute(final, "transition_reason"),
        },
        "final_is_unknown_attempt": legacy_attempt is not None,
    }


def _case_pair_local(occurrence: Mapping[str, Any], record: Mapping[str, Any]):
    """`StableCasePairRef` のうち結果に依らない部分（strategy と 2 つの case）。"""
    pair = lookup(record, "pair_or_case")
    if builtin_sequence(pair) and size(pair) == 2:
        first, second = elements_of(pair)
        attempt_identity = _or(lookup(occurrence, "attempt_identity"), {})
        strategy = builtin_str(_or(lookup(attempt_identity, "strategy_identity"), "unknown"))
        return (strategy, identity_tuple(first), identity_tuple(second))
    return None


class IdentityPool:
    """結果 1 件の中で繰り返される identity を 1 度だけ持つための表。

    proof requirement key と legacy obligation id は同じ値が原因間・
    `all`/`active` 間で何度も現れ、そのまま並べると aggregate の 4 割を占める
    （固定 subset 実測）。値は捨てずに index 参照へ畳む（可逆）。
    """

    def __init__(self) -> None:
        self._index: Dict[str, int] = {}
        self.items: List[Any] = []

    def intern(self, value: Any) -> int:
        key = repr(freeze_identity(value))
        found = self._index.get(key)
        if found is None:
            found = len(self.items)
            self._index[key] = found
            self.items.append(value)
        return found


def resolve_pool_refs(pool: Sequence[Any], refs: Any) -> List[Any]:
    """`*_refs` の index 列を実体へ戻す（読み取り側が使う）。"""
    items = list(pool or ())
    resolved: List[Any] = []
    for ref in refs or ():
        try:
            index = int(ref)
        except (TypeError, ValueError):
            continue
        if 0 <= index < len(items):
            resolved.append(items[index])
    return resolved


@dataclass
class _CauseGroup:
    occurrence_count: int = 0
    occurrence_ids: Dict[Any, Any] = field(default_factory=dict)
    reason_ids: set = field(default_factory=set)
    decision_effects: set = field(default_factory=set)
    required: set = field(default_factory=set)
    legacy: set = field(default_factory=set)
    evidence: set = field(default_factory=set)
    certainties: set = field(default_factory=set)
    case_pairs: set = field(default_factory=set)
    proof_requirements_complete: bool = True

    def to_dict(self) -> Dict[str, Any]:
        return {
            "occurrence_count": self.occurrence_count,
            "occurrence_ids": [self.occurrence_ids[key] for key in _by_repr(self.occurrence_ids)],
            "reason_ids": _by_repr(self.reason_ids),
            "decision_effects": _by_repr(self.decision_effects),
            "required_proof_id_refs": sorted(self.required),
            "proof_requirements_complete": self.proof_requirements_complete,
            "legacy_proof_obligation_id_refs": sorted(self.legacy),
            "evidence_refs": _by_repr(self.evidence),
            "certainties": _by_repr(self.certainties),
            "case_pairs": _by_repr(self.case_pairs),
        }


def _by_repr(values: Iterable[Any]) -> List[Any]:
    """組み込みの値（写し・文字列）の集合を `repr` の順に。"""
    return sorted(values, key=repr)


def _add_to_group(
    group: _CauseGroup, *, occurrence_id_payload: Any, frozen_occurrence_id: Any, record: Any,
    required: Tuple[Any, ...], complete: bool, pair: Any, certainty: str, pool: IdentityPool,
) -> None:
    """occurrence 1 件を原因の union（`_CauseGroup`）へ足す。

    Issue #22 PR-22-D: `record` / `occurrence_id_payload` は trace の表現（live な葉を持ち得る）なので、
    `live_values` の `lookup` / `elements_of` / `as_bool` だけで読む。group の集合へ入れるのは
    組み込みの値（`builtin_str`・`freeze_identity` の写し）だけで、payload はそのまま置く。
    """

    group.occurrence_count += 1
    if frozen_occurrence_id not in group.occurrence_ids:
        group.occurrence_ids[frozen_occurrence_id] = occurrence_id_payload
    group.reason_ids.add(builtin_str(_or(lookup(record, "reason_id"), "unknown")))
    group.decision_effects.add(builtin_str(_or(lookup(record, "decision_effect"), "")))
    group.required.update(pool.intern(item) for item in elements_of(required))
    if not live_values.as_bool(complete):
        group.proof_requirements_complete = False
    legacy = lookup(record, "proof_obligation_id")
    if _truthy(legacy):
        group.legacy.add(pool.intern(freeze_identity(legacy)))
    group.evidence.update(builtin_str(item) for item in _elements(lookup(record, "evidence_refs")))
    group.certainties.add(certainty)
    if pair is not None:
        group.case_pairs.add(pair)


def _cause_key_digest(cause: Mapping[str, Any]) -> str:
    return cause["cause_key_digest"]


def _build_root_causes(
    binary_identities: Tuple[Any, Any],
    *,
    occurrences: Sequence[Mapping[str, Any]],
    transitions: Sequence[Mapping[str, Any]],
    completions: Sequence[Mapping[str, Any]],
    reason_completions: Sequence[Mapping[str, Any]],
    attempts: Sequence[Any],
    diagnostics: Dict[str, int],
    final_identity: Any = None,
):
    left_identity, right_identity = elements_of(binary_identities)
    left = identity_tuple(left_identity)
    right = identity_tuple(right_identity)
    transition_state = resolve_occurrence_transitions(
        occurrences,
        transitions,
        completions,
        diagnostics,
        reason_completions=reason_completions,
    )
    final_ids = set()
    if final_identity is None:
        final_identity = _final_attempt_identity(attempts, occurrences)
    if final_identity is not None:
        final_ids = {
            freeze_identity(lookup(item, "occurrence_id"))
            for item in occurrences
            if freeze_identity(lookup(item, "attempt_identity")) == final_identity
        }

    pool = IdentityPool()
    groups: Dict[Any, Dict[str, Any]] = {}
    total_reasons = typed_reasons = explicit_status = pair_identified = 0
    for occurrence in occurrences:
        record = _or(lookup(occurrence, "reason_record"), {})
        total_reasons += 1
        status = builtin_str(_or(lookup(occurrence, "initial_causal_status"), "unclassified"))
        if status != "unclassified":
            explicit_status += 1
        occurrence_id_payload = lookup(occurrence, "occurrence_id")
        occurrence_id = freeze_identity(occurrence_id_payload)
        effective = transition_state.get(occurrence_id, status)
        resolution = resolve_cause_identity(
            typed_cause_key=lookup(record, "typed_cause_key"),
            object_target_key=lookup(record, "object_target_key"),
            left_binary_identity=left,
            right_binary_identity=right,
        )
        if resolution.diagnostic:
            _bump(diagnostics, resolution.diagnostic)
        if not resolution.resolved:
            _bump(diagnostics, "unkeyed_reason_record")
            continue
        typed_reasons += int(resolution.typed)
        pair = _case_pair_local(occurrence, record)
        if pair is not None:
            pair_identified += 1
        certainty = "explicit" if status != "unclassified" else "unclassified"
        is_final = occurrence_id in final_ids
        if status == "unclassified" and is_final:
            effect = builtin_str(_or(lookup(record, "decision_effect"), ""))
            action_status = builtin_str(_or(lookup(record, "action_status"), ""))
            if effect in BLOCKING_DECISION_EFFECTS and action_status != "proof_complete":
                certainty = "inferred_final_attempt"
                effective = "active_final_blocker"
        coerced = coerce_unknown_reason_record(_plain_reason_payload(record))
        proofs = resolve_required_proofs(
            proof_requirement_ids=_or(lookup(record, "proof_requirement_ids"), ()),
            object_target_key=lookup(record, "object_target_key"),
            identity_scope=resolution.identity_scope,
            canonical_cause_key=resolution.canonical_cause_key,
            recovery_actions=build_unknown_recovery_actions((coerced,), work=_diagnostic_work()),
        )
        for name in elements_of(proofs.diagnostics):
            _bump(diagnostics, builtin_str(name))

        group_key = (resolution.identity_scope, resolution.cause_kind, resolution.canonical_cause_key)
        entry = groups.get(group_key)
        if entry is None:
            entry = {
                "resolution": resolution,
                "all": _CauseGroup(),
                "active": _CauseGroup(),
                "active_count": 0,
                "status_counts": {},
            }
            groups[group_key] = entry
        _add_to_group(
            entry["all"], occurrence_id_payload=occurrence_id_payload,
            frozen_occurrence_id=occurrence_id, record=record, required=proofs.keys,
            complete=proofs.complete, pair=pair, certainty=certainty, pool=pool,
        )
        _inc(entry["status_counts"], builtin_str(effective or "unclassified"))
        # active は「最終 attempt の occurrence」かつ「実効 status が blocker」の
        # ときだけ。`all` と別に union するので、active に数えなかった occurrence の
        # proof requirement や case pair が active 側へ混ざらない。
        if effective in _ACTIVE_CAUSAL_STATUSES and is_final:
            _add_to_group(
                entry["active"], occurrence_id_payload=occurrence_id_payload,
                frozen_occurrence_id=occurrence_id, record=record, required=proofs.keys,
                complete=proofs.complete, pair=pair, certainty=certainty, pool=pool,
            )
            entry["active_count"] += 1

    root_causes = [_freeze_cause(entry) for entry in groups.values()]
    root_causes.sort(key=_cause_key_digest)
    stats_pool = list(pool.items)
    stats = {
        "total_reasons": total_reasons,
        "typed_reasons": typed_reasons,
        "explicit_causal_status": explicit_status,
        "pair_identified": pair_identified,
        "transition_target_count": len({
            freeze_identity(lookup(item, "target_occurrence_id"))
            for item in transitions
            if builtin_mapping(item) is not None and _truthy(lookup(item, "target_occurrence_id"))
        }),
        "proof_completion_count": 0,
        "linked_completion_count": 0,
        "diagnostics": diagnostics,
    }
    completion_ids = {
        freeze_identity(lookup(item, "completion_id"))
        for item in completions
        if builtin_mapping(item) is not None and _truthy(lookup(item, "completion_id"))
    }
    stats["proof_completion_count"] = len(completion_ids)
    stats["linked_completion_count"] = len({
        freeze_identity(lookup(item, "cause_ref"))
        for item in transitions
        if builtin_mapping(item) is not None
        and json_scalar(lookup(item, "cause_kind")) == "proof_completion"
        and freeze_identity(lookup(item, "cause_ref")) in completion_ids
    })
    return root_causes, stats, stats_pool


def _freeze_cause(entry: Mapping[str, Any]) -> Dict[str, Any]:
    resolution: CauseIdentityResolution = entry["resolution"]
    all_group: _CauseGroup = entry["all"]
    active_group: _CauseGroup = entry["active"]
    status_counts = dict(entry["status_counts"])
    if entry["active_count"]:
        causal_status = "active"
    elif status_counts and all(
        status in _RESOLVED_CAUSAL_STATUSES for status in status_counts
    ):
        causal_status = "completed"
    else:
        causal_status = "unknown"
    # 1 つの cause identity に複数の reason が乗ることがある。代表値はここに、
    # 集合は `all` に置く（代表値だけを見て集合を推測しないこと）。
    reason_ids = sorted(all_group.reason_ids)
    effects = sorted(all_group.decision_effects)
    case_pairs = sorted(all_group.case_pairs, key=repr)
    return {
        "cause_key_digest": identity_digest(
            (resolution.identity_scope, resolution.cause_kind, resolution.canonical_cause_key)
        ),
        "identity_scope": resolution.identity_scope,
        "cause_kind": resolution.cause_kind,
        "canonical_cause_key": resolution.canonical_cause_key,
        "typed": resolution.typed,
        "reason_id": reason_ids[0] if reason_ids else None,
        "decision_effect": effects[0] if effects else None,
        "required_proof_id_refs": sorted(all_group.required),
        "causal_status": causal_status,
        "causal_status_counts": status_counts,
        "affected_case_pair_digest": identity_digest(case_pairs) if case_pairs else None,
        "occurrence_count": all_group.occurrence_count,
        "active_occurrence_count": entry["active_count"],
        "all": all_group.to_dict(),
        "active": active_group.to_dict() if entry["active_count"] else None,
    }


def completion_counts(
    completions: Sequence[Mapping[str, Any]],
    reason_completions: Sequence[Mapping[str, Any]],
    occurrences: Sequence[Mapping[str, Any]],
) -> Dict[str, Any]:
    """完了イベントの集計。backlog（未完了）とは独立に数える。"""
    requirement_to_reasons: Dict[Any, set] = {}
    for occurrence in occurrences:
        record = _or(lookup(occurrence, "reason_record"), {})
        reason_id = builtin_str(_or(lookup(record, "reason_id"), "unknown"))
        for requirement in _elements(lookup(record, "proof_requirement_ids")):
            try:
                key = _requirement_key(requirement)
            except (TypeError, ValueError):
                continue
            requirement_to_reasons.setdefault(freeze_identity(key), set()).add(reason_id)

    proof_by_kind: Dict[str, int] = {}
    proof_by_status: Dict[str, int] = {}
    proof_by_reason: Dict[str, int] = {}
    for event in completions:
        requirement = lookup(event, "proof_requirement_id")
        proof_kind = builtin_str(
            _or(lookup(_or(requirement, {}), "proof_kind"), UNKNOWN_TUPLE_MISSING)
        )
        _inc(proof_by_kind, proof_kind)
        _inc(proof_by_status, builtin_str(_or(lookup(event, "proof_status"), UNKNOWN_TUPLE_MISSING)))
        matched = ()
        if builtin_mapping(requirement) is not None:
            try:
                key = freeze_identity(_requirement_key(requirement))
            except (TypeError, ValueError):
                key = None
            if key is not None:
                matched = tuple(sorted(requirement_to_reasons.get(key, ())))
        for reason_id in matched or ("(unmatched)",):
            _inc(proof_by_reason, reason_id)

    occurrence_reason = {
        freeze_identity(lookup(item, "occurrence_id")): builtin_str(
            _or(lookup(_or(lookup(item, "reason_record"), {}), "reason_id"), "unknown")
        )
        for item in occurrences
    }
    reason_by_reason: Dict[str, int] = {}
    reason_by_status: Dict[str, int] = {}
    for event in reason_completions:
        target = freeze_identity(lookup(event, "completed_occurrence_id"))
        _inc(reason_by_reason, occurrence_reason.get(target, "(unmatched)"))
        _inc(reason_by_status, builtin_str(
            _or(lookup(event, "applicability_status"), UNKNOWN_TUPLE_MISSING)
        ))

    return {
        "proof_completions": {
            "total": size(completions),
            "by_proof_kind": proof_by_kind,
            "by_proof_status": proof_by_status,
            "by_reason": proof_by_reason,
        },
        "reason_completions": {
            "total": size(reason_completions),
            "by_reason": reason_by_reason,
            "by_applicability_status": reason_by_status,
        },
    }


def transition_counts(
    transitions: Sequence[Mapping[str, Any]],
    occurrences: Sequence[Mapping[str, Any]],
) -> Dict[str, Any]:
    initial_status = {
        freeze_identity(lookup(item, "occurrence_id")): builtin_str(
            _or(lookup(item, "initial_causal_status"), "unclassified")
        )
        for item in occurrences
    }
    by_kind: Dict[str, int] = {}
    by_status_pair: Dict[str, int] = {}
    for transition in transitions:
        kind = builtin_str(_or(lookup(transition, "transition_kind"), UNKNOWN_TUPLE_MISSING))
        _inc(by_kind, kind)
        target = freeze_identity(lookup(transition, "target_occurrence_id"))
        prior = initial_status.get(target, "(unmatched)")
        _inc(by_status_pair, f"{prior}->{kind}")
    return {
        "causal_transitions": {
            "total": size(transitions),
            "by_transition_kind": by_kind,
            "by_status_pair": by_status_pair,
        },
    }
