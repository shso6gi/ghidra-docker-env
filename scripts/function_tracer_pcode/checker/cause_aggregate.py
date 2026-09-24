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
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.builtin_containers import builtin_mapping, builtin_sequence
from scripts.function_tracer_pcode.core.json_encoding import (
    CANONICAL,
    LEGACY,
    NOT_PLAIN as _NOT_PLAIN_SCALAR,
    builtin_str,
    builtin_view,
    exception_text,
    plain_scalar,
    is_json_record,
    object_identity_token,
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

def freeze_identity(value: Any) -> Any:
    """dict / list / tuple を比較可能な frozen 表現へ正規化する。

    JSON 往復で tuple が list になっても同じ値になるので、`debug_trace` 経路と
    `unknown_cause_aggregate` 経路の identity が一致する。

    Issue #22 PR-22-D: 組み込みの振る舞いの容器だけを辿り、葉は組み込みで書ける値（文字列・
    scalar・組み込みのままの enum）だけをそのまま残す。それ以外の葉（上書きした `__hash__` /
    `__repr__` を持ち得る live な object）は object の identity の印にする（`object_identity_token`。
    旧実装の既定の `hash` と同じく object ごとに区別し、集計は印を hash・`repr` するだけで object の
    code を呼ばない）。JSON から読んだ値（reporting）は常に組み込みの値なので変わらない。
    """
    mapping = builtin_mapping(value)
    if mapping is not None:
        return tuple(
            (builtin_str(key), freeze_identity(item))
            for key, item in sorted(mapping.items(), key=lambda pair: builtin_str(pair[0]))
        )
    if builtin_sequence(value):
        return tuple(freeze_identity(item) for item in value)
    ok, view = builtin_view(value)
    if ok:
        # scalar の subclass（JPype の `JInt` など）は基底型の値（同じ `str` / `hash` / `==`）
        return view
    return object_identity_token(value)


def identity_tuple(value: Any) -> Tuple[Any, ...]:
    frozen = freeze_identity(value)
    if frozen is None:
        return ()
    return frozen if isinstance(frozen, tuple) else (frozen,)


def _jsonable(value: Any) -> Any:
    mapping = builtin_mapping(value)
    if mapping is not None:
        return {
            builtin_str(key): _jsonable(item)
            for key, item in sorted(mapping.items(), key=lambda pair: builtin_str(pair[0]))
        }
    if builtin_sequence(value):
        return [_jsonable(item) for item in value]
    if isinstance(value, (str, int, float, bool)) or value is None:
        return value
    return builtin_str(value)


def identity_digest(value: Any) -> str:
    """identity の安定した digest（tuple/list の違いに依らない）。"""
    payload = json.dumps(
        _jsonable(freeze_identity(value)),
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
    """

    if isinstance(typed_cause_key, Mapping):
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
            identity_scope=cause.identity_scope,
            cause_kind=cause.cause_kind,
            canonical_cause_key=canonical_cause_tuple(cause),
            typed=True,
        )
    if not object_target_key:
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
    if isinstance(value, tuple):
        if value and value[0] == tag:
            return True
        return any(contains_tagged_identity(item, tag) for item in value)
    return False


@dataclass(frozen=True)
class RequiredProofResolution:
    keys: Tuple[Tuple[Any, ...], ...] = ()
    complete: bool = True
    diagnostics: Tuple[str, ...] = ()


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
    explicit = tuple(proof_requirement_ids or ())
    for requirement in explicit:
        try:
            keys.append(ProofRequirementId.from_dict(requirement).to_key())
        except (TypeError, ValueError) as exc:
            complete = False
            message = exception_text(exc, 200)
            if "unsupported proof requirement schema" in message:
                diagnostics.append("unknown_proof_requirement_schema")
            elif "requires kind, target, and contract" in message:
                diagnostics.append("proof_requirement_identity_incomplete")
            else:
                diagnostics.append("invalid_proof_requirement")
    if not explicit and object_target_key:
        for action in recovery_actions:
            proof_kind = builtin_str(getattr(action, "proof_kind", "none"))
            if proof_kind == "none":
                continue
            contract = (
                "legacy_recovery_contract",
                proof_kind,
                freeze_identity(getattr(action, "required_evidence", ()) or ()),
            )
            try:
                requirement = ProofRequirementId.create(
                    proof_kind,
                    ("legacy_scope_aware_target", identity_scope, canonical_cause_key),
                    contract,
                )
            except ValueError:
                continue
            keys.append(requirement.to_key())
    return RequiredProofResolution(tuple(keys), complete, tuple(diagnostics))


# ---------------------------------------------------------------------------
# 因果（completion / transition）の解決（reporting と共有）
# ---------------------------------------------------------------------------

def attempt_ordinal(value: Any) -> Optional[int]:
    if not isinstance(value, Mapping):
        return None
    raw = value.get("attempt_ordinal")
    try:
        return int(raw)
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
        freeze_identity(item.get("occurrence_id")): item for item in occurrences
    }
    occurrence_ids = set(occurrence_by_id)
    result: Dict[Any, str] = {}
    for completion in reason_completions:
        if not isinstance(completion, Mapping):
            continue
        target = freeze_identity(completion.get("completed_occurrence_id"))
        if builtin_str(completion.get("applicability_status")) != "APPLICABLE":
            _bump(diagnostics, "inapplicable_reason_completion")
            continue
        if target not in occurrence_ids:
            _bump(diagnostics, "dangling_reason_completion_target")
            continue
        record = occurrence_by_id[target].get("reason_record") or {}
        expected_target = freeze_identity(record.get("object_target_key"))
        observed_target = freeze_identity(completion.get("exact_target_id"))
        expected_slots = {
            builtin_str(item.get("proof_kind") or "")
            for item in (record.get("proof_requirement_ids") or ())
            if isinstance(item, Mapping)
        }
        observed_slot = builtin_str(completion.get("exact_missing_fact_or_proof_slot") or "")
        if (
            (expected_target and expected_target != observed_target)
            or (expected_slots and observed_slot not in expected_slots)
            or not completion.get("source_snapshot_fingerprint")
            or not completion.get("semantic_seed_or_premise_digest")
            or not completion.get("evidence_or_artifact_digest")
            or not completion.get("recognizing_stage")
        ):
            _bump(diagnostics, "invalid_reason_completion_applicability")
            continue
        completed_ordinal = attempt_ordinal(completion.get("completed_at_attempt"))
        target_ordinal = attempt_ordinal(occurrence_by_id[target].get("attempt_identity"))
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
    for transition in sorted(transitions, key=lambda item: repr(freeze_identity(item))):
        if not isinstance(transition, Mapping):
            continue
        transition_id = freeze_identity(transition.get("transition_id"))
        if transition_id in seen:
            continue
        seen.add(transition_id)
        target = freeze_identity(transition.get("target_occurrence_id"))
        if target not in occurrence_ids:
            _bump(diagnostics, "dangling_transition_target")
            continue
        kind = builtin_str(transition.get("transition_kind") or "")
        cause_kind = builtin_str(transition.get("cause_kind") or "")
        cause_ref = freeze_identity(transition.get("cause_ref"))
        valid = False
        emitted_ordinal = attempt_ordinal(transition.get("emitted_at_attempt"))
        target_ordinal = attempt_ordinal(occurrence_by_id[target].get("attempt_identity"))
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
        aggregation_key = builtin_str(record.aggregation_unit or "result")
        unit_key = record.pair_or_case or record.stage
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
        PRIMARY_DECISION_EFFECT_PRIORITY.get(builtin_str(record.decision_effect), 99),
        builtin_str(record.reason_id),
        builtin_str(record.reason_scope),
        builtin_str(record.recovery_proof_kind),
        builtin_str(record.proof_stage or ""),
        builtin_str(record.action_status or ""),
        tuple(builtin_str(ref) for ref in (record.evidence_refs or ())),
        builtin_str(record.detail or ""),
    )


def is_proof_backlog(record: UnknownReasonRecord, actions: Sequence[Any] = ()) -> bool:
    action_statuses = {builtin_str(getattr(action, "status", "")) for action in actions}
    return (
        record.reason_class in PROOF_BACKLOG_CLASSES
        or record.action_status
        in {
            UnknownRecoveryActionStatus.PENDING_PROOF.value,
            UnknownRecoveryActionStatus.PLANNED.value,
        }
        or (
            record.object_target_key is not None
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
        builtin_str(record.reason_id),
        builtin_str(record.decision_effect),
        builtin_str(record.reason_scope),
        builtin_str(record.recovery_proof_kind or UNKNOWN_TUPLE_MISSING),
        builtin_str(record.proof_stage or UNKNOWN_TUPLE_MISSING),
        builtin_str(record.action_status or UNKNOWN_TUPLE_MISSING),
    )


def global_reason_tuple_from_action(action: Any) -> Tuple[str, ...]:
    return (
        builtin_str(getattr(action, "count_kind", UnknownCountKind.PROOF_ACTION.value)),
        builtin_str(getattr(action, "reason_id", UnknownReasonId.UNKNOWN.value)),
        builtin_str(getattr(action, "decision_effect", UNKNOWN_TUPLE_MISSING)),
        builtin_str(getattr(action, "reason_scope", UNKNOWN_TUPLE_MISSING)),
        builtin_str(getattr(action, "proof_kind", UNKNOWN_TUPLE_MISSING)),
        builtin_str(getattr(action, "proof_stage", UNKNOWN_TUPLE_MISSING)),
        builtin_str(getattr(action, "status", UNKNOWN_TUPLE_MISSING)),
    )


def recovery_action_key(action: Any) -> str:
    return " | ".join(
        builtin_str(value)
        for value in (
            getattr(action, "reason_id", "unknown"),
            getattr(action, "proof_kind", "none"),
            getattr(action, "proof_stage", "unspecified"),
            getattr(action, "status", "unspecified"),
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
    detail = bounded_text(getattr(record, "detail", None), DETAIL_MAX_CHARS, work=work)
    return f"{record.reason_id} | {detail if detail else '(no detail)'}"


def build_reason_view(records: Sequence[UnknownReasonRecord]) -> Dict[str, Any]:
    """record 集合 1 つ分の集計。`summarize_validation_unknowns` と同じ次元。

    空の record 集合でも「0 件」として view を返す。view を作るかどうか
    （= その源の証拠があるか）は呼び出し側が決める。reporting 側の
    「record が 1 件も無い結果」の合成は結果単位の話なのでここではしない。
    """

    records = tuple(records)
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
        _inc(record_multiset, global_reason_tuple_from_record(
            record, UnknownCountKind.REASON_RECORD.value
        ))
        for action in build_unknown_recovery_actions((record,)):
            _inc(action_multiset, global_reason_tuple_from_action(action))

    for record in primary:
        _inc(by_reason_detail, reason_detail_key(record))
        _inc(validation_multiset, global_reason_tuple_from_record(
            record, UnknownCountKind.VALIDATION_UNKNOWN_UNIT.value
        ))
        _inc(by_reason, record.reason_id)
        _inc(by_decision_effect, record.decision_effect)
        _inc(by_reason_scope, record.reason_scope)
        actions = build_unknown_recovery_actions((record,))
        if is_proof_backlog(record, actions):
            _inc(backlog_by_reason, record.reason_id)
            for action in actions:
                _inc(backlog_by_proof_kind, action.proof_kind)
                _inc(backlog_by_recovery_action, recovery_action_key(action))
                _inc(backlog_by_action_status, action.status)
        else:
            _inc(operational_by_reason, record.reason_id)
            _inc(operational_by_class, record.reason_class)

    return {
        "unit_count": len(primary),
        "record_count": len(records),
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
        for key, value in sorted(counts.items(), key=lambda item: tuple(builtin_str(part) for part in item[0]))
    ]


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
    count_key = key if isinstance(key, tuple) else builtin_str(key)
    counts[count_key] = int(counts.get(count_key, 0) or 0) + int(amount)


# ---------------------------------------------------------------------------
# aggregate の生成
# ---------------------------------------------------------------------------

def attach_cause_aggregate(result: Any) -> None:
    """canonical bundle を組む前に aggregate を確定して結果へ載せる。

    `to_dict()` は field が無ければ自分で組むので、この呼び出しは「preimage を
    作る前に一度だけ確定させる」ためのもの。preimage 確定後に payload を
    書き換えてはならない（`checker/diagnostics.py` の digest 契約と同じ）。
    """
    from scripts.function_tracer_pcode.core.budget_policy import serialization_scope

    # Issue #22 PR-22-D: 集計が読む値（canonical reason・準備済みの trace 部分）は、authority
    # 確定後の field に空けた headroom を上限にした診断用の作業量へ数えながら読む（超えれば
    # `error` を持つ値 = 診断の marker。判定は変えない）
    prepared = getattr(result, "prepared_semantic_payload", None)
    plan = getattr(prepared, "plan", None)
    limit = getattr(plan, "headroom_bytes", None) if plan is not None and plan.max_bytes is not None else None
    try:
        with serialization_scope(
            site=AGGREGATE_SITE, target_parts=("unknown_cause_aggregate",),
            terminal=False, max_bytes=limit, enabled=limit is not None,
        ):
            result.unknown_cause_aggregate = build_unknown_cause_aggregate(result)
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

    trace = getattr(result, "debug_trace", None)
    # 集計は trace の列を直接読むので、読む要素の大きさを 1 つずつ作業量へ数えてから読む
    # （集計の作業は数えた入力で抑えられる）
    attempts = tuple(_metered(getattr(trace, "attempts", ()), mode=LEGACY)) if trace is not None else ()
    occurrences = _trace_occurrence_views(attempts)
    transitions = _event_views(_metered(
        getattr(trace, "causal_transitions", ()) if trace is not None else (), mode=LEGACY,
    ))
    completions = _event_views(_metered(
        getattr(trace, "proof_completion_events", ()) if trace is not None else (), mode=LEGACY,
    ))
    reason_completions = _event_views(_metered(
        getattr(trace, "reason_completion_events", ()) if trace is not None else (), mode=LEGACY,
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
        "has_trace_occurrences": bool(occurrences),
        "legacy_view": legacy_view,
        "attempts": _attempt_summary(attempts, legacy_attempt) if trace is not None else None,
    }
    if occurrences:
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
        evidence.update({
            "root_causes": root_causes,
            "root_cause_stats": root_cause_stats,
            "identity_pool": identity_pool,
            "completions": (
                completion_counts(completions, reason_completions, occurrences)
                if trace is not None else None
            ),
            "transitions": transition_counts(transitions, occurrences) if trace is not None else None,
        })
    else:
        # root cause は authority 後に canonical reason から作る（trace の event だけ残す）
        evidence.update({
            "transition_events": transitions,
            "completion_events": completions,
            "reason_completion_events": reason_completions,
            "final_attempt_identity": _final_attempt_identity(attempts, ()),
        })
    return evidence


#: authority 確定後に集計を作る観測点（診断用の作業量）。
AGGREGATE_SITE = "checker.cause_aggregate.attach"


def _metered(values: Any, *, mode: str):
    """集計が読む列を、1 要素ずつ今の直列化の作業量へ数えてから渡す（入力を先に写さない）。

    * authority 確定 **前** の trace（live な記録）は `LEGACY`（集計が読む形そのもの）で数える。
    * authority 確定 **後** の canonical reason は `CANONICAL`（出力と同じ有界な行: 封印済みの
      key は `cause:<id>` の要約で、辿らない）で数える。

    作業量（`serialization_scope` の診断用の work）を超えれば、そこで
    `JsonBudgetExhausted` が上がり、集計は `error` を持つ値になる（fail open）。作業量の
    scope の外（部品単体の呼び出し）では数えない。
    """

    from scripts.function_tracer_pcode.core.budget_policy import active_serialization_work
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    work = active_serialization_work()
    for value in values or ():
        if work is not None:
            RESULT_JSON_POLICY.count_into(value, work, mode=mode)
        yield value


def trace_evidence_is_usable(evidence: Any) -> bool:
    return (
        isinstance(evidence, Mapping)
        and evidence.get("schema") == TRACE_CAUSE_EVIDENCE_SCHEMA
        and not evidence.get("error")
    )


def _build_unknown_cause_aggregate(result: Any) -> Dict[str, Any]:
    evidence = _prepared_trace_evidence(result)
    if evidence is None:
        # pair 境界を通らずに組んだ結果（test の直接構築など）: その場で作る
        evidence = build_trace_cause_evidence(
            result,
            binary_identities=(
                getattr(result, "binary1_content_identity", None),
                getattr(result, "binary2_content_identity", None),
            ),
        )
    if not trace_evidence_is_usable(evidence):
        detail = None
        if isinstance(evidence, Mapping):
            detail = evidence.get("error") or evidence.get("reason")
        return {
            "schema": UNKNOWN_CAUSE_AGGREGATE_SCHEMA,
            "error": ("trace_evidence_unavailable: " + builtin_str(detail))[:200],
        }
    trace_present = bool(evidence.get("trace_present"))

    canonical_records = coerce_unknown_reason_records(
        _metered(getattr(result, "unknown_reasons", ()), mode=CANONICAL)
    )
    canonical_available = getattr(result, "decision_receipt", None) is not None

    final_reasons = build_reason_view(canonical_records) if canonical_available else None
    # `legacy_view` は「trace を見た consumer が診断に使う record 集合」の集計で、
    # **trace を観測できたときだけ**作る。trace がもともと無い結果では `null` に
    # して、「観測できなかった」と「観測して 0 件」を取り違えさせない。
    # `source` はどちらの record 集合を選んだかで、consumer の選択規則と一致する:
    #   final_attempt   -- 最終 UNKNOWN/TIMEOUT attempt の record（0 件もあり得る）
    #   payload_records -- 最終 attempt が無いので結果の `unknown_reasons`
    legacy_view = None
    if trace_present:
        if evidence.get("has_final_attempt"):
            legacy_view = evidence.get("legacy_view")
        else:
            legacy_view = build_reason_view(canonical_records)
            legacy_view["source"] = "payload_records"
    effective_view = final_reasons if final_reasons is not None else legacy_view
    effective_source = (
        "canonical" if final_reasons is not None
        else ("legacy" if legacy_view is not None else None)
    )

    if evidence.get("has_trace_occurrences"):
        root_causes = evidence.get("root_causes")
        root_cause_stats = evidence.get("root_cause_stats")
        identity_pool = evidence.get("identity_pool")
        completions_block = evidence.get("completions")
        transitions_block = evidence.get("transitions")
    else:
        # trace に occurrence が無い: root cause は canonical reason（authority の出力）から
        occurrences = _payload_occurrence_views(canonical_records)
        transitions = list(evidence.get("transition_events") or ())
        completions = list(evidence.get("completion_events") or ())
        reason_completions = list(evidence.get("reason_completion_events") or ())
        diagnostics: Dict[str, int] = {}
        root_causes, root_cause_stats, identity_pool = _build_root_causes(
            (
                getattr(result, "binary1_content_identity", None),
                getattr(result, "binary2_content_identity", None),
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
        "backlog": dict(effective_view["backlog"]) if effective_view is not None else None,
        "operational": dict(effective_view["operational"]) if effective_view is not None else None,
        "completions": completions_block,
        "transitions": transitions_block,
        "root_causes": root_causes,
        "identity_pool": identity_pool,
        "root_cause_stats": root_cause_stats,
        "attempts": evidence.get("attempts") if trace_present else None,
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
    prepared = getattr(result, "prepared_semantic_payload", None)
    cause_evidence = getattr(prepared, "cause_evidence", None)
    if cause_evidence is None:
        return None
    return cause_evidence.value()


def _trace_occurrence_views(attempts: Sequence[Any]) -> List[Dict[str, Any]]:
    """trace の occurrence 列（`root_blocker_summary._extract_occurrences` と同じ）。"""
    occurrences: List[Dict[str, Any]] = []
    for attempt in attempts:
        for occurrence in tuple(getattr(attempt, "reason_occurrences", ()) or ()):
            occurrences.append(_as_mapping(occurrence))
    return occurrences


def _payload_occurrence_views(records: Sequence[UnknownReasonRecord]) -> List[Dict[str, Any]]:
    """trace に occurrence が無いときの occurrence 列（結果の reason から作る）。

    Issue #22 PR-22-D: record は出力と同じ有界な表現で読む（authority 後に大きい key を
    辿り直さない。root cause の identity は `typed_cause_key` から決まる）。
    """
    identity = {"trace_schema_version": 1, "strategy_identity": "payload", "attempt_ordinal": 0}
    occurrences: List[Dict[str, Any]] = []
    for ordinal, record in enumerate(records):
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
    """record を出力と同じ有界な行にし、書いた byte を今の直列化の作業量へ足す。

    record ごとに残りの作業量を上限にし、使った分を足していく（record ごとに作業量の全体を
    使い直さない）。作業量の scope の外（部品単体の呼び出し）では数えない。
    """

    from scripts.function_tracer_pcode.core.budget_policy import active_serialization_work
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    work = active_serialization_work()
    if work is None:
        return RESULT_JSON_POLICY.prepare(record).value()
    prepared = RESULT_JSON_POLICY.prepare(record, max_bytes=work.remaining())
    work.charge(prepared.encoded_bytes)
    return prepared.value()


def _payload_final_identity(evidence: Mapping[str, Any], occurrences: Sequence[Mapping[str, Any]]):
    identity = evidence.get("final_attempt_identity")
    if identity is not None:
        return freeze_identity(identity)
    if occurrences:
        return freeze_identity(occurrences[-1].get("attempt_identity"))
    return None


def _event_views(values: Iterable[Any]) -> List[Dict[str, Any]]:
    return [_as_mapping(value) for value in (values or ())]


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

    payload = dict(record)
    for key in _STRINGIFIED_REASON_FIELDS:
        if payload.get(key) is not None:
            payload[key] = _plain_reason_value(payload[key])
    refs = payload.get("evidence_refs")
    if refs:
        payload["evidence_refs"] = tuple(_plain_reason_value(ref) for ref in refs)
    return payload


def _as_mapping(value: Any) -> Dict[str, Any]:
    # 組み込みの振る舞いの mapping と json record（`to_dict()` は `materialize` が作業量の中で
    # 作る）だけを読む。それ以外の object の `to_dict()`（任意の producer）は呼ばない
    mapping = builtin_mapping(value)
    if mapping is not None:
        return dict(mapping)
    if is_json_record(value):
        payload = value.to_dict()
        if builtin_mapping(payload) is not None:
            return dict(payload)
    return {}


def _final_legacy_attempt(trace: Any, attempts: Sequence[Any]):
    """legacy 最終 attempt（`_extract_final_unknown_reasons` の legacy 分岐と同条件）。"""
    if trace is None or getattr(trace, "final_result", None) is not None:
        return None, ()
    for attempt in reversed(tuple(attempts)):
        if (
            getattr(attempt, "result", None) is None
            and builtin_str(getattr(attempt, "transition_reason", "")) in FINAL_UNKNOWN_TRANSITIONS
        ):
            return attempt, coerce_unknown_reason_records(
                getattr(attempt, "unknown_reasons", ()) or ()
            )
    return None, ()


def _final_attempt_identity(attempts: Sequence[Any], occurrences: Sequence[Mapping[str, Any]]):
    for attempt in reversed(tuple(attempts)):
        if (
            getattr(attempt, "result", None) is None
            and builtin_str(getattr(attempt, "transition_reason", "")) in FINAL_UNKNOWN_TRANSITIONS
        ):
            return freeze_identity({
                "trace_schema_version": 1,
                "strategy_identity": builtin_str(
                    getattr(attempt, "strategy", None) or getattr(attempt, "phase", None) or "unknown"
                ),
                "attempt_ordinal": int(getattr(attempt, "attempt_id", 0) or 0),
            })
    if occurrences:
        return freeze_identity(occurrences[-1].get("attempt_identity"))
    return None


def _attempt_summary(attempts: Sequence[Any], legacy_attempt: Any) -> Dict[str, Any]:
    final = legacy_attempt if legacy_attempt is not None else (attempts[-1] if attempts else None)
    return {
        "count": len(attempts),
        "final": None if final is None else {
            "strategy": getattr(final, "strategy", None),
            "attempt_id": getattr(final, "attempt_id", None),
            "transition_reason": getattr(final, "transition_reason", None),
        },
        "final_is_unknown_attempt": legacy_attempt is not None,
    }


def _case_pair_local(occurrence: Mapping[str, Any], record: Mapping[str, Any]):
    """`StableCasePairRef` のうち結果に依らない部分（strategy と 2 つの case）。"""
    pair = record.get("pair_or_case")
    if isinstance(pair, (tuple, list)) and len(pair) == 2:
        strategy = builtin_str((occurrence.get("attempt_identity") or {}).get("strategy_identity") or "unknown")
        return (strategy, identity_tuple(pair[0]), identity_tuple(pair[1]))
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

    def add(self, *, occurrence_id_payload, frozen_occurrence_id, record, required, complete,
            pair, certainty, pool: IdentityPool) -> None:
        self.occurrence_count += 1
        self.occurrence_ids.setdefault(frozen_occurrence_id, occurrence_id_payload)
        self.reason_ids.add(builtin_str(record.get("reason_id") or "unknown"))
        self.decision_effects.add(builtin_str(record.get("decision_effect") or ""))
        self.required.update(pool.intern(item) for item in required)
        if not complete:
            self.proof_requirements_complete = False
        legacy = record.get("proof_obligation_id")
        if legacy:
            self.legacy.add(pool.intern(freeze_identity(legacy)))
        self.evidence.update(builtin_str(item) for item in (record.get("evidence_refs") or ()))
        self.certainties.add(certainty)
        if pair is not None:
            self.case_pairs.add(pair)

    def to_dict(self) -> Dict[str, Any]:
        ordered = lambda values: sorted(values, key=repr)
        return {
            "occurrence_count": self.occurrence_count,
            "occurrence_ids": [self.occurrence_ids[key] for key in ordered(self.occurrence_ids)],
            "reason_ids": ordered(self.reason_ids),
            "decision_effects": ordered(self.decision_effects),
            "required_proof_id_refs": sorted(self.required),
            "proof_requirements_complete": self.proof_requirements_complete,
            "legacy_proof_obligation_id_refs": sorted(self.legacy),
            "evidence_refs": ordered(self.evidence),
            "certainties": ordered(self.certainties),
            "case_pairs": ordered(self.case_pairs),
        }


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
    left = identity_tuple(binary_identities[0])
    right = identity_tuple(binary_identities[1])
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
            freeze_identity(item.get("occurrence_id"))
            for item in occurrences
            if freeze_identity(item.get("attempt_identity")) == final_identity
        }

    pool = IdentityPool()
    groups: Dict[Any, Dict[str, Any]] = {}
    total_reasons = typed_reasons = explicit_status = pair_identified = 0
    for occurrence in occurrences:
        record = occurrence.get("reason_record") or {}
        total_reasons += 1
        status = builtin_str(occurrence.get("initial_causal_status") or "unclassified")
        if status != "unclassified":
            explicit_status += 1
        occurrence_id = freeze_identity(occurrence.get("occurrence_id"))
        effective = transition_state.get(occurrence_id, status)
        resolution = resolve_cause_identity(
            typed_cause_key=record.get("typed_cause_key"),
            object_target_key=record.get("object_target_key"),
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
            effect = builtin_str(record.get("decision_effect") or "")
            action_status = builtin_str(record.get("action_status") or "")
            if effect in BLOCKING_DECISION_EFFECTS and action_status != "proof_complete":
                certainty = "inferred_final_attempt"
                effective = "active_final_blocker"
        coerced = coerce_unknown_reason_record(_plain_reason_payload(record))
        proofs = resolve_required_proofs(
            proof_requirement_ids=record.get("proof_requirement_ids") or (),
            object_target_key=record.get("object_target_key"),
            identity_scope=resolution.identity_scope,
            canonical_cause_key=resolution.canonical_cause_key,
            recovery_actions=build_unknown_recovery_actions((coerced,)),
        )
        for name in proofs.diagnostics:
            _bump(diagnostics, name)

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
        contribution = dict(
            occurrence_id_payload=occurrence.get("occurrence_id"),
            frozen_occurrence_id=occurrence_id,
            record=record,
            required=proofs.keys,
            complete=proofs.complete,
            pair=pair,
            certainty=certainty,
            pool=pool,
        )
        entry["all"].add(**contribution)
        _inc(entry["status_counts"], builtin_str(effective or "unclassified"))
        # active は「最終 attempt の occurrence」かつ「実効 status が blocker」の
        # ときだけ。`all` と別に union するので、active に数えなかった occurrence の
        # proof requirement や case pair が active 側へ混ざらない。
        if effective in _ACTIVE_CAUSAL_STATUSES and is_final:
            entry["active"].add(**contribution)
            entry["active_count"] += 1

    root_causes = [_freeze_cause(entry) for entry in groups.values()]
    root_causes.sort(key=lambda item: item["cause_key_digest"])
    stats_pool = list(pool.items)
    stats = {
        "total_reasons": total_reasons,
        "typed_reasons": typed_reasons,
        "explicit_causal_status": explicit_status,
        "pair_identified": pair_identified,
        "transition_target_count": len({
            freeze_identity(item.get("target_occurrence_id"))
            for item in transitions
            if isinstance(item, Mapping) and item.get("target_occurrence_id")
        }),
        "proof_completion_count": 0,
        "linked_completion_count": 0,
        "diagnostics": diagnostics,
    }
    completion_ids = {
        freeze_identity(item.get("completion_id"))
        for item in completions
        if isinstance(item, Mapping) and item.get("completion_id")
    }
    stats["proof_completion_count"] = len(completion_ids)
    stats["linked_completion_count"] = len({
        freeze_identity(item.get("cause_ref"))
        for item in transitions
        if isinstance(item, Mapping)
        and item.get("cause_kind") == "proof_completion"
        and freeze_identity(item.get("cause_ref")) in completion_ids
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
        record = occurrence.get("reason_record") or {}
        reason_id = builtin_str(record.get("reason_id") or "unknown")
        for requirement in record.get("proof_requirement_ids") or ():
            try:
                key = ProofRequirementId.from_dict(requirement).to_key()
            except (TypeError, ValueError):
                continue
            requirement_to_reasons.setdefault(freeze_identity(key), set()).add(reason_id)

    proof_by_kind: Dict[str, int] = {}
    proof_by_status: Dict[str, int] = {}
    proof_by_reason: Dict[str, int] = {}
    for event in completions:
        requirement = event.get("proof_requirement_id")
        proof_kind = builtin_str((requirement or {}).get("proof_kind") or UNKNOWN_TUPLE_MISSING)
        _inc(proof_by_kind, proof_kind)
        _inc(proof_by_status, builtin_str(event.get("proof_status") or UNKNOWN_TUPLE_MISSING))
        matched = ()
        if isinstance(requirement, Mapping):
            try:
                key = freeze_identity(ProofRequirementId.from_dict(requirement).to_key())
            except (TypeError, ValueError):
                key = None
            if key is not None:
                matched = tuple(sorted(requirement_to_reasons.get(key, ())))
        for reason_id in matched or ("(unmatched)",):
            _inc(proof_by_reason, reason_id)

    occurrence_reason = {
        freeze_identity(item.get("occurrence_id")): builtin_str(
            (item.get("reason_record") or {}).get("reason_id") or "unknown"
        )
        for item in occurrences
    }
    reason_by_reason: Dict[str, int] = {}
    reason_by_status: Dict[str, int] = {}
    for event in reason_completions:
        target = freeze_identity(event.get("completed_occurrence_id"))
        _inc(reason_by_reason, occurrence_reason.get(target, "(unmatched)"))
        _inc(reason_by_status, builtin_str(event.get("applicability_status") or UNKNOWN_TUPLE_MISSING))

    return {
        "proof_completions": {
            "total": len(completions),
            "by_proof_kind": proof_by_kind,
            "by_proof_status": proof_by_status,
            "by_reason": proof_by_reason,
        },
        "reason_completions": {
            "total": len(reason_completions),
            "by_reason": reason_by_reason,
            "by_applicability_status": reason_by_status,
        },
    }


def transition_counts(
    transitions: Sequence[Mapping[str, Any]],
    occurrences: Sequence[Mapping[str, Any]],
) -> Dict[str, Any]:
    initial_status = {
        freeze_identity(item.get("occurrence_id")): builtin_str(
            item.get("initial_causal_status") or "unclassified"
        )
        for item in occurrences
    }
    by_kind: Dict[str, int] = {}
    by_status_pair: Dict[str, int] = {}
    for transition in transitions:
        kind = builtin_str(transition.get("transition_kind") or UNKNOWN_TUPLE_MISSING)
        _inc(by_kind, kind)
        target = freeze_identity(transition.get("target_occurrence_id"))
        prior = initial_status.get(target, "(unmatched)")
        _inc(by_status_pair, f"{prior}->{kind}")
    return {
        "causal_transitions": {
            "total": len(transitions),
            "by_transition_kind": by_kind,
            "by_status_pair": by_status_pair,
        },
    }
