# -*- coding: utf-8 -*-
"""結果の出力を authority 確定 **前** に有界に準備する（Issue #22 PR-22-D）。

順序（`authority/lifecycle/production_boundary.py` が呼ぶ）:

```text
legacy の意味解析結果
  ↓ G4-a  台帳に限界 / 内部バグ → pair 単位の結果
  ↓ G4-b  prepare_pair_output():  OutputPreparer.prepare(result)
            収まる  → PreparedSemanticPayload（+ SerializationPlan、headroom 予約済み）
            超える  → raise_limitation(PAIR_TERMINAL_LIMITATION)
                      → pair 単位の UNKNOWN → その小さい結果を prepare し直す
  ↓ connector.finish(...)              # 最初の不可逆な判定
  ↓ reconciliation / canonical decision / relations / conditional lane
CLI:
  build_final_result_envelope(result, seal=...)
     = prepared（A） + authority（B） + metadata（C）→ 封印 → bounded encode
```

**receipt を発行した後で判定を UNKNOWN に差し替える経路は無い**: 大きさの判定は
`connector.finish` より前に済んでいる。

payload の所有者は 3 層に分かれる（`RESULT_FIELDS` が唯一の対応表）:

* **A. `PreparedSemanticPayload`** — 解析由来の（重くなり得る）field。authority
  確定前に JSON 値へ落として凍結し、以後は元の object を読み直さない。legacy の
  `unknown_reasons` は `raw_limitation_evidence` として持つだけで、最終 JSON の
  `unknown_reasons` には使わない。
* **B. `AuthorityDecisionEnvelope`** — 判定・canonical reason・relations・receipt・
  conditional lane の結果。authority の attach_* が結果へ書いた値 **だけ** を読む。
  A の同名 field で上書きしない（そもそも同名 field を持たない）。
* **C. `OutputMetadata`** — 診断・時間・content identity など判定に関わらない
  field。上限を超えるときは切り詰めてよい（件数 + marker）。

authority 確定後に足される B / C のために、A は `BudgetPolicy.envelope_headroom_bytes`
を空けて準備する。最終 encoder は B を **切り詰めない**。C を切り詰めても収まら
なければそれは headroom 契約の違反（`OutputEnvelopeInvariantViolation`）で、
意味の限界ではない — 確定した判定を UNKNOWN へ変えない。

依存の向き: checker → core（予算・JSON policy）/ authority（receipt の公開表現）。
solver の実行・identity・renderer には依存しない
（`tests/unit/test_architecture_boundaries.py`）。
"""

from __future__ import annotations

import copy
from dataclasses import dataclass
from enum import Enum
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.core.budget_policy import (
    BudgetKind,
    BudgetPolicy,
    active_budget_policy,
    budget_observations,
    observe_budget_usage,
    raise_expression_size_budget_exceeded,
)
from scripts.function_tracer_pcode.core.errors import (
    AnalysisFailureError,
    AnalysisLimitation,
    InternalError,
    record_internal_bug,
)
from scripts.function_tracer_pcode.core.json_encoding import (
    RESULT_JSON_POLICY,
    JsonEncodingPolicy,
    JsonOutputLimitExceeded,
)


#: 準備した payload の大きさを予算と比べる観測点。
PREPARATION_SITE = "checker.output_preparation.prepare"
#: 最終 envelope の大きさを確かめる観測点（authority 確定後）。
FINAL_ENVELOPE_SITE = "output.final_envelope"


class FieldOwner(str, Enum):
    """結果 JSON の field を **誰が決めるか**。"""

    PREPARED = "prepared"    # A: authority 確定前に準備・凍結する解析由来の値
    AUTHORITY = "authority"  # B: authority の attach_* が決めた値
    METADATA = "metadata"    # C: 判定に関わらない診断・時間・identity


@dataclass(frozen=True)
class OutputField:
    """結果 JSON の 1 field。`produce(result)` は (出すか, 値) を返す。"""

    key: str
    owner: FieldOwner
    produce: Callable[[Any], Tuple[bool, Any]]
    #: 上限を超えるときに件数 + marker へ置き換えてよいか（診断だけ）
    truncatable: bool = False


def _always(getter: Callable[[Any], Any]) -> Callable[[Any], Tuple[bool, Any]]:
    return lambda result: (True, getter(result))


def _when(test: Callable[[Any], bool], getter: Callable[[Any], Any]):
    return lambda result: (True, getter(result)) if test(result) else (False, None)


def _to_dict_or_none(value: Any) -> Any:
    return value.to_dict() if value else None


# -- A: 解析由来の値 ----------------------------------------------------------


def _signature(getter):
    return lambda result: (True, _to_dict_or_none(getter(result)))


def _mips64_abi_constraints(result) -> Dict[str, Any]:
    return {
        key: {"signedness": value[0], "narrow_bits": value[1]}
        for key, value in result.mips64_abi_constraints.items()
    }


# -- B: authority が決めた値 --------------------------------------------------


def _decision_receipt(result) -> Any:
    if result.decision_receipt is not None:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            decision_receipt_payload,
            outcome_from_result,
        )

        outcome_from_result(result)
        return decision_receipt_payload(result.decision_receipt)
    if result.canonical_decision_required:
        raise ValueError("canonical serialization lacks DecisionReceipt")
    return None


def _conditional_decision_receipt(result) -> Any:
    if result.conditional_decision_receipt is not None:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            conditional_decision_receipt_payload,
        )

        return conditional_decision_receipt_payload(result.conditional_decision_receipt)
    if result.conditional_outcome is not None:
        raise ValueError("conditional outcome without its ConditionalDecisionReceipt")
    return None


def _unknown_recovery_backlog(result) -> Any:
    from scripts.function_tracer_pcode.checker.unknown_reason import (
        summarize_unknown_recovery_backlog,
    )

    return summarize_unknown_recovery_backlog(result.unknown_reasons)


# -- C: 判定に関わらない値 ----------------------------------------------------


def _diagnostics(result) -> Any:
    from scripts.function_tracer_pcode.checker.diagnostics import result_diagnostics_payload

    return result_diagnostics_payload(result)


def _unknown_cause_aggregate(result) -> Any:
    # Issue #128: 原因分析の compact 集計は常時出す。既に確定していればそれを
    # 使い、ここで作り直さない（preimage 確定前に固定するため）。
    if result.unknown_cause_aggregate is None:
        from scripts.function_tracer_pcode.checker.cause_aggregate import (
            build_unknown_cause_aggregate,
        )

        result.unknown_cause_aggregate = build_unknown_cause_aggregate(result)
    return result.unknown_cause_aggregate


_A = FieldOwner.PREPARED
_B = FieldOwner.AUTHORITY
_C = FieldOwner.METADATA

#: 結果 JSON の field と所有者の **唯一の対応表**（並びは従来の `to_dict()` の
#: key 順）。field を足すときはここへ 1 行足す: 所有者を書けば、準備・合成・
#: 大きさの勘定・切り詰めの可否はそれに従う。判定に関わらない診断を足すだけなら
#: `_C` の行を足す（authority・identity・solver 側は変わらない、M-3）。
RESULT_FIELDS: Tuple[OutputField, ...] = (
    OutputField("is_equivalent", _B, _always(lambda r: r.is_equivalent)),
    OutputField("function1_name", _A, _always(lambda r: r.function1_name)),
    OutputField("function2_name", _A, _always(lambda r: r.function2_name)),
    OutputField("binary1_name", _A, _always(lambda r: r.binary1_name)),
    OutputField("binary2_name", _A, _always(lambda r: r.binary2_name)),
    # content identity は `check_from_binaries` が boundary の **後** に書く
    OutputField("binary1_content_identity", _C, _always(lambda r: r.binary1_content_identity)),
    OutputField("binary2_content_identity", _C, _always(lambda r: r.binary2_content_identity)),
    OutputField("function1_identity", _A, _always(lambda r: r.function1_identity)),
    OutputField("function2_identity", _A, _always(lambda r: r.function2_identity)),
    OutputField("function1_signature", _A, _signature(lambda r: r.function1_signature)),
    OutputField("function2_signature", _A, _signature(lambda r: r.function2_signature)),
    OutputField(
        "effective_function1_signature", _A,
        _signature(lambda r: r.get_effective_function1_signature()),
    ),
    OutputField(
        "effective_function2_signature", _A,
        _signature(lambda r: r.get_effective_function2_signature()),
    ),
    OutputField(
        "function1_signature_hypotheses", _A,
        _always(lambda r: list(r.function1_signature_hypotheses)),
    ),
    OutputField(
        "function2_signature_hypotheses", _A,
        _always(lambda r: list(r.function2_signature_hypotheses)),
    ),
    OutputField("solver_results", _A, _always(lambda r: _to_dict_or_none(r.solver_results))),
    OutputField("counterexample", _A, _always(lambda r: _to_dict_or_none(r.counterexample))),
    OutputField("total_time", _C, _always(lambda r: r.total_time)),
    OutputField("error_message", _B, _always(lambda r: r.error_message)),
    OutputField("failure_status", _B, _always(lambda r: r.failure_status)),
    OutputField("failure_message", _B, _always(lambda r: r.failure_message)),
    OutputField("type_fix_result", _A, _always(lambda r: _to_dict_or_none(r.type_fix_result))),
    OutputField("retry_count", _A, _always(lambda r: r.retry_count)),
    OutputField("is_timeout", _B, _always(lambda r: r.is_timeout())),
    OutputField("final_outcome", _B, _always(lambda r: r.final_outcome)),
    OutputField("decision_receipt", _B, _always(_decision_receipt)),
    OutputField("conditional_outcome", _B, _always(lambda r: r.conditional_outcome)),
    OutputField(
        "conditional_decision_receipt", _B, _always(_conditional_decision_receipt),
    ),
    OutputField(
        "c_active_base", _B, _always(lambda r: [dict(row) for row in r.canonical_c_active_base]),
    ),
    OutputField(
        "q_open_base", _B, _always(lambda r: [dict(row) for row in r.canonical_q_open_base]),
    ),
    OutputField("constrained_fragments", _A, _always(lambda r: r.constrained_fragments)),
    OutputField("pairwise_stats", _A, _always(lambda r: r.pairwise_stats)),
    OutputField("pairwise_debug_stats", _A, _always(lambda r: r.pairwise_debug_stats)),
    OutputField(
        "unknown_reasons", _B,
        _always(lambda r: [reason.to_dict() for reason in r.unknown_reasons]),
    ),
    OutputField(
        "unknown_recovery_actions", _B,
        _always(lambda r: [action.to_dict() for action in r.unknown_recovery_actions]),
    ),
    OutputField("unknown_recovery_backlog", _B, _always(_unknown_recovery_backlog)),
    OutputField(
        "decision_gated_by_pending_proof", _B,
        _always(lambda r: r.decision_gated_by_pending_proof),
    ),
    OutputField("sat_pair_info", _A, _always(lambda r: r.sat_pair_info)),
    OutputField("stage_path", _A, _always(lambda r: r.stage_path)),
    OutputField("diagnostics", _C, _always(_diagnostics), truncatable=True),
    OutputField(
        "unknown_cause_aggregate", _C, _always(_unknown_cause_aggregate), truncatable=True,
    ),
    OutputField(
        "canonical_result_finalization_bundle", _B,
        _when(
            lambda r: r.canonical_result_finalization_bundle is not None,
            lambda r: dict(r.canonical_result_finalization_bundle),
        ),
    ),
    OutputField(
        "completed_recovery_proof_evidence", _A,
        _when(
            lambda r: bool(r.completed_recovery_proof_evidence),
            lambda r: list(r.completed_recovery_proof_evidence),
        ),
    ),
    OutputField(
        "reason_completion_applicability_contexts", _A,
        _when(
            lambda r: bool(r.reason_completion_applicability_contexts),
            lambda r: list(r.reason_completion_applicability_contexts),
        ),
    ),
    OutputField(
        "call_effect_shadow_manifest", _A,
        _when(
            lambda r: r.call_effect_shadow_manifest is not None,
            lambda r: dict(r.call_effect_shadow_manifest),
        ),
    ),
    OutputField(
        "call_proof_terminal_provenance", _A,
        _when(
            lambda r: r.call_proof_terminal_provenance is not None,
            lambda r: dict(r.call_proof_terminal_provenance),
        ),
    ),
    OutputField(
        "recurrence_promotion_receipt", _A,
        _when(
            lambda r: r.recurrence_promotion_receipt is not None,
            lambda r: dict(r.recurrence_promotion_receipt),
        ),
    ),
    OutputField(
        "decisive_proof_provenance", _A,
        _when(
            lambda r: r.decisive_proof_provenance is not None,
            lambda r: dict(r.decisive_proof_provenance),
        ),
    ),
    OutputField(
        "identical_fast_path_disposition", _A,
        _when(
            lambda r: r.identical_fast_path_disposition is not None,
            lambda r: dict(r.identical_fast_path_disposition),
        ),
    ),
    OutputField(
        "identical_function_identity_evidence", _A,
        _when(
            lambda r: r.identical_function_identity_evidence is not None,
            lambda r: dict(r.identical_function_identity_evidence),
        ),
    ),
    OutputField(
        "mips64_abi_constraints", _A,
        _when(lambda r: bool(r.mips64_abi_constraints), _mips64_abi_constraints),
    ),
    # Issue #128 PR-128-B: trace は常に object 上に在り、debug 指定のときだけ
    # JSON へ添付する。判定に関わらないので、予算を超えるなら件数 + marker に
    # 置き換える（debug 出力が判定を変えることはない）。
    OutputField(
        "debug_trace", _A,
        _when(lambda r: bool(r.debug_trace) and r.emit_debug_trace, lambda r: r.debug_trace.to_dict()),
        truncatable=True,
    ),
)

FIELD_BY_KEY: Dict[str, OutputField] = {item.key: item for item in RESULT_FIELDS}


def fields_owned_by(owner: FieldOwner) -> Tuple[str, ...]:
    return tuple(item.key for item in RESULT_FIELDS if item.owner is owner)


#: A の値を作るために読む結果の属性。準備の後にこれらが **差し替えられた**
#: なら、準備した値はもう結果を表していない（`PreparedPayloadStale`）。
_PREPARED_SOURCE_ATTRIBUTES = (
    "function1_name", "function2_name", "binary1_name", "binary2_name",
    "function1_identity", "function2_identity",
    "function1_signature", "function2_signature",
    "effective_function1_signature", "effective_function2_signature",
    "function1_signature_hypotheses", "function2_signature_hypotheses",
    "solver_results", "counterexample", "type_fix_result", "retry_count",
    "constrained_fragments", "pairwise_stats", "pairwise_debug_stats",
    "sat_pair_info", "stage_path",
    "completed_recovery_proof_evidence", "reason_completion_applicability_contexts",
    "call_effect_shadow_manifest", "call_proof_terminal_provenance",
    "recurrence_promotion_receipt", "decisive_proof_provenance",
    "identical_fast_path_disposition", "identical_function_identity_evidence",
    "mips64_abi_constraints", "debug_trace",
)

_SCALARS = (str, int, float, bool, type(None))


class PreparedPayloadStale(AnalysisFailureError):
    """準備した後で A の元になる属性が差し替えられた（内部バグ）。"""


class OutputEnvelopeInvariantViolation(AnalysisFailureError):
    """authority 確定後の field が予約した headroom に収まらなかった。

    **意味の限界ではない**。判定は確定済みなので UNKNOWN へ変えず、出力の契約
    違反（内部エラー）として扱う（`FINAL_ENVELOPE_SITE`）。
    """

    def __init__(self, message: str, *, max_bytes: int, requested_bytes: int) -> None:
        super().__init__(message)
        self.max_bytes = int(max_bytes)
        self.requested_bytes = int(requested_bytes)


# ---------------------------------------------------------------------------
# A: 準備
# ---------------------------------------------------------------------------


def _opaque_value_bytes(value: Any) -> int:
    return len(type(value).__qualname__) + 2


#: 置き換えた診断の中身（件数 + marker）。
def _truncation_marker(key: str, value: Any, size: int) -> Dict[str, Any]:
    count = len(value) if isinstance(value, (list, tuple, dict)) else None
    return {
        "truncated": True,
        "field": key,
        "reason": BudgetKind.SERIALIZATION_BYTES.value,
        "original_bytes": int(size),
        "original_items": count,
    }


@dataclass(frozen=True)
class SerializationPlan:
    """準備した payload の大きさと予約の内訳（診断に出す、判定には使わない）。"""

    encoding: JsonEncodingPolicy
    #: 結果 JSON 全体の上限（`None` は無制限）
    max_bytes: Optional[int]
    #: authority 確定後の field のために空けた byte 数
    headroom_bytes: int
    #: A の field が結果 JSON の中で占める byte 数（key・区切りを含む）
    prepared_bytes: int
    #: field ごとの (key, byte 数, 表現)。表現は `json` か `truncation_marker`
    field_bytes: Tuple[Tuple[str, int, str], ...]

    @property
    def prepared_max_bytes(self) -> Optional[int]:
        if self.max_bytes is None:
            return None
        return self.max_bytes - self.headroom_bytes

    def to_diagnostic(self) -> Dict[str, Any]:
        largest = sorted(self.field_bytes, key=lambda row: (-row[1], row[0]))[:5]
        return {
            "max_bytes": self.max_bytes,
            "headroom_bytes": self.headroom_bytes,
            "prepared_bytes": self.prepared_bytes,
            "prepared_max_bytes": self.prepared_max_bytes,
            "truncated_fields": [
                key for key, _size, shape in self.field_bytes if shape != "json"
            ],
            "largest_fields": [
                {"field": key, "bytes": size} for key, size, _shape in largest
            ],
        }


@dataclass(frozen=True)
class PreparedSemanticPayload:
    """authority 確定前に作る解析由来の payload（A）。作った後は元の object を読まない。

    **canonical な判定も canonical reason も持たない**。legacy の reason は
    `raw_limitation_evidence`（reason id と stage）として残すだけ。
    """

    fields: Tuple[Tuple[str, Any], ...]
    raw_limitation_evidence: Tuple[Tuple[str, Optional[str]], ...]
    plan: SerializationPlan
    #: 準備に使った属性値（差し替え検出用。判定にも出力にも使わない）
    _sources: Tuple[Tuple[str, Any], ...] = ()

    def keys(self) -> Tuple[str, ...]:
        return tuple(key for key, _value in self.fields)

    def values_for_output(self) -> Dict[str, Any]:
        """出力へ置く値の **複製**（呼び出し側が壊しても準備済みの値は変わらない）。"""

        return {key: copy.deepcopy(value) for key, value in self.fields}

    def check_current(self, result: Any) -> None:
        """準備の後で A の元になる属性が差し替えられていないか。"""

        for name, original in self._sources:
            current = getattr(result, name, None)
            if current is original:
                continue
            if isinstance(current, _SCALARS) and isinstance(original, _SCALARS) and (
                type(current) is type(original) and current == original
            ):
                continue
            raise PreparedPayloadStale(
                f"result.{name} was replaced after the output was prepared"
            )


class OutputPreparer:
    """A を 1 回だけ準備する。**大きさの判定と予算超過の変換はここだけ**。"""

    def __init__(
        self,
        policy: BudgetPolicy,
        *,
        encoding: JsonEncodingPolicy = RESULT_JSON_POLICY,
    ) -> None:
        if type(policy) is not BudgetPolicy:
            raise TypeError("output preparation needs an exact BudgetPolicy")
        self.policy = policy
        self.encoding = encoding

    def _item_bytes(self, key: str, value: Any, limit: Optional[int]) -> int:
        """`"key": value` と前の区切りを合わせた byte 数（`limit` で飽和）。

        JSON にならない値（CLI の encoder なら `TypeError` になる値）は型名の長さで
        数える: 準備は `--emit-result-json` の有無に関わらず全 pair で走るので、
        ここで例外にすると従来は起きなかった失敗を作ってしまう。JSON にできるかの
        判定は従来どおり最終 encoder が行う。
        """

        encoding = self.encoding
        overhead = (
            encoding.string_bytes(key)
            + len(encoding.key_separator.encode("utf-8"))
            + len(encoding.item_separator.encode("utf-8"))
        )
        remaining = None if limit is None else max(0, limit - overhead)
        return overhead + encoding.value_bytes(
            value, max_bytes=remaining, opaque_bytes=_opaque_value_bytes,
        )

    def prepare(self, result: Any) -> PreparedSemanticPayload:
        """A を準備する。意味の field が収まらなければ限界にする（raise）。

        診断扱いの field（`truncatable`）は、収まらなければ件数 + marker に置き
        換える — debug 出力の有無で判定が変わってはいけない。
        """

        limit = self.policy.prepared_payload_limit()
        values: List[Tuple[str, Any]] = []
        sizes: List[Tuple[str, int, str]] = []
        deferred: List[Tuple[str, Any]] = []
        used = 0
        for item in RESULT_FIELDS:
            if item.owner is not FieldOwner.PREPARED:
                continue
            present, value = item.produce(result)
            if not present:
                continue
            # 結果の live な list / dict を共有しない（後から書き換えられても
            # 準備した値は変わらない）
            value = copy.deepcopy(value)
            if item.truncatable:
                deferred.append((item.key, value))
                continue
            remaining = None if limit is None else limit - used
            size = self._item_bytes(item.key, value, remaining)
            used += size
            sizes.append((item.key, size, "json"))
            values.append((item.key, value))
            if limit is not None and used > limit:
                self._raise_exceeded(used, sizes)
        for key, value in deferred:
            remaining = None if limit is None else limit - used
            size = self._item_bytes(key, value, remaining)
            if limit is not None and used + size > limit:
                full = self._item_bytes(key, value, None)
                value = _truncation_marker(key, value, full)
                size = self._item_bytes(key, value, None)
                shape = "truncation_marker"
            else:
                shape = "json"
            used += size
            sizes.append((key, size, shape))
            values.append((key, value))
        if limit is not None and used > limit:
            self._raise_exceeded(used, sizes)
        order = {item.key: index for index, item in enumerate(RESULT_FIELDS)}
        values.sort(key=lambda row: order[row[0]])
        plan = SerializationPlan(
            encoding=self.encoding,
            max_bytes=self.policy.serialization_bytes,
            headroom_bytes=self.policy.envelope_headroom_bytes,
            prepared_bytes=used,
            field_bytes=tuple(sizes),
        )
        observe_budget_usage(
            BudgetKind.SERIALIZATION_BYTES,
            used + self.policy.envelope_headroom_bytes,
            site=PREPARATION_SITE,
        )
        return PreparedSemanticPayload(
            fields=tuple(values),
            raw_limitation_evidence=tuple(
                (reason.reason_id, getattr(reason, "stage", None))
                for reason in (getattr(result, "unknown_reasons", None) or ())
            ),
            plan=plan,
            _sources=tuple(
                (name, getattr(result, name, None))
                for name in _PREPARED_SOURCE_ATTRIBUTES
            ),
        )

    def _raise_exceeded(self, used: int, sizes: List[Tuple[str, int, str]]) -> None:
        largest = max(sizes, key=lambda row: row[1])[0] if sizes else None
        raise_expression_size_budget_exceeded(
            BudgetKind.SERIALIZATION_BYTES,
            observed=used + self.policy.envelope_headroom_bytes,
            limit=self.policy.serialization_bytes,
            site=PREPARATION_SITE,
            target_key=("result_payload", largest),
            evidence=(
                f"prepared_bytes={used}",
                f"headroom_bytes={self.policy.envelope_headroom_bytes}",
                f"largest_field={largest}",
            ),
        )


def _attach_budget_diagnostics(result: Any, prepared: PreparedSemanticPayload, policy) -> None:
    """予算の値・観測値・準備の内訳を診断へ書く（C、判定に使わない）。"""

    diagnostics = dict(getattr(result, "diagnostics", None) or {})
    diagnostics["expression_budget"] = {
        "policy": policy.to_diagnostic(),
        "observed": budget_observations(),
        "serialization": prepared.plan.to_diagnostic(),
    }
    result.diagnostics = diagnostics


def prepare_pair_output(
    checker: Any,
    result: Any,
    *,
    function_name1: str,
    function_name2: str,
    start_time: float,
) -> Any:
    """G4-b: authority 確定前に出力を準備する（収まらなければ pair 単位の限界）。

    限界は `raise_limitation` で台帳へ記録してから raise されるので、ここでは
    既存の変換（`apply_pair_failure_gate`）に渡すだけで reason 付き UNKNOWN
    （pilot 無しなら `limitation_unattributed` の ERROR）になる。その小さい結果を
    同じ preparer で準備し直す。それも収まらないのは内部バグ（UNKNOWN 用の
    結果は解析由来の重い field を持たない）。
    """

    if result is None:
        return result
    from scripts.function_tracer_pcode.checker.pair_execution import (
        apply_pair_failure_gate,
    )

    policy = active_budget_policy()
    preparer = OutputPreparer(policy)
    try:
        prepared = preparer.prepare(result)
    except AnalysisLimitation:
        result = apply_pair_failure_gate(
            checker,
            result,
            function_name1=function_name1,
            function_name2=function_name2,
            start_time=start_time,
        )
        try:
            prepared = preparer.prepare(result)
        except AnalysisLimitation as exc:
            bug = InternalError(exc, site=PREPARATION_SITE)
            record_internal_bug(bug, site=PREPARATION_SITE)
            result = apply_pair_failure_gate(
                checker,
                result,
                function_name1=function_name1,
                function_name2=function_name2,
                start_time=start_time,
            )
            prepared = OutputPreparer(BudgetPolicy.unlimited()).prepare(result)
    _attach_budget_diagnostics(result, prepared, policy)
    result.prepared_semantic_payload = prepared
    return result


# ---------------------------------------------------------------------------
# B / C と合成
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class AuthorityDecisionEnvelope:
    """authority が確定した field（B）。authority の attach_* が書いた値だけを読む。"""

    fields: Tuple[Tuple[str, Any], ...]

    @classmethod
    def from_result(cls, result: Any) -> "AuthorityDecisionEnvelope":
        return cls(tuple(_produce(result, FieldOwner.AUTHORITY)))


@dataclass(frozen=True)
class OutputMetadata:
    """判定に関わらない field（C）。上限を超えるなら切り詰めてよい。"""

    fields: Tuple[Tuple[str, Any], ...]

    @classmethod
    def from_result(cls, result: Any) -> "OutputMetadata":
        return cls(tuple(_produce(result, FieldOwner.METADATA)))


def _produce(result: Any, owner: FieldOwner) -> Iterable[Tuple[str, Any]]:
    for item in RESULT_FIELDS:
        if item.owner is not owner:
            continue
        present, value = item.produce(result)
        if present:
            yield item.key, value


def assemble_result_payload(
    prepared: PreparedSemanticPayload,
    authority: AuthorityDecisionEnvelope,
    metadata: OutputMetadata,
    *,
    include_debug_trace: bool = True,
) -> Dict[str, Any]:
    """A + B + C を従来の key 順で 1 つの dict にする（大きさは見ない）。

    同じ key を 2 つの層が持つことは無い（`RESULT_FIELDS` が所有者を 1 つに
    決めている）。念のため重なりは内部エラーにする — B を A で上書きする経路を
    作らないため。

    `include_debug_trace` は「trace を JSON へ添付するか」という出力の選択
    （`EquivalenceResult.emit_debug_trace`）。trace の **中身** は準備時の値で、
    ここで読み直すことはない: 準備時に添付しない指定だった trace は、後から
    指定を変えても現れない（準備していないので）。
    """

    prepared_values = prepared.values_for_output()
    if not include_debug_trace:
        prepared_values.pop("debug_trace", None)
    parts: Dict[str, Any] = {}
    for layer in (prepared_values, dict(authority.fields), dict(metadata.fields)):
        overlap = set(parts) & set(layer)
        if overlap:
            raise ValueError(f"output fields owned twice: {sorted(overlap)}")
        parts.update(layer)
    return {item.key: parts[item.key] for item in RESULT_FIELDS if item.key in parts}


def prepared_payload_for(result: Any) -> PreparedSemanticPayload:
    """結果の A（準備済みならそれ、無ければ上限無しで今準備する）。

    準備済みでないのは pair 境界を通らずに組んだ結果（test の直接構築、起動
    失敗・import 失敗の ERROR）だけで、どれも解析由来の重い値を持たない。
    """

    prepared = getattr(result, "prepared_semantic_payload", None)
    if prepared is None:
        return OutputPreparer(BudgetPolicy.unlimited()).prepare(result)
    prepared.check_current(result)
    return prepared


def result_payload(result: Any) -> Dict[str, Any]:
    """`EquivalenceResult.to_dict()` の本体（A は準備済みの値、B / C は今の値）。"""

    return assemble_result_payload(
        prepared_payload_for(result),
        AuthorityDecisionEnvelope.from_result(result),
        OutputMetadata.from_result(result),
        include_debug_trace=bool(getattr(result, "emit_debug_trace", True)),
    )


@dataclass(frozen=True)
class FinalResultEnvelope:
    """CLI が書く最終 payload と、その JSON 文字列（policy 共有の bounded encoder）。"""

    payload: Dict[str, Any]
    text: str
    plan: SerializationPlan
    total_bytes: int
    truncated_metadata: Tuple[str, ...]

    def size_line(self) -> str:
        prepared = self.plan.prepared_bytes
        return (
            f"total={self.total_bytes} prepared={prepared} "
            f"authority_and_metadata={self.total_bytes - prepared} "
            f"headroom={self.plan.headroom_bytes} limit={self.plan.max_bytes} "
            f"truncated_metadata={','.join(self.truncated_metadata) or '-'}"
        )


def build_final_result_envelope(
    result: Any,
    *,
    seal: Optional[Callable[[Dict[str, Any]], Mapping[str, Any]]] = None,
) -> FinalResultEnvelope:
    """A + B + C → 封印 → bounded encode。**Expression / 解析 object を辿らない**。

    上限は準備したときの plan（authority 確定前に決めた値）。超えるときは C の
    切り詰め可能な field を件数 + marker に置き換えてから封印し直す（封印は
    preimage 全体の digest を持つので、封印後に payload を変えない）。B は
    切り詰めない。それでも超えるなら `OutputEnvelopeInvariantViolation`。
    """

    prepared = prepared_payload_for(result)
    plan = prepared.plan
    encoding = plan.encoding
    limit = plan.max_bytes
    authority = AuthorityDecisionEnvelope.from_result(result)
    metadata = dict(OutputMetadata.from_result(result).fields)
    truncated: List[str] = []

    def _sealed(meta: Dict[str, Any]) -> Tuple[Dict[str, Any], int]:
        preimage = assemble_result_payload(
            prepared, authority, OutputMetadata(tuple(meta.items())),
            include_debug_trace=bool(getattr(result, "emit_debug_trace", True)),
        )
        payload = dict(preimage)
        if seal is not None:
            payload["canonical_result_finalization_bundle"] = dict(seal(preimage))
        return payload, encoding.value_bytes(payload, max_bytes=limit)

    payload, size = _sealed(metadata)
    if limit is not None and size > limit:
        for item in RESULT_FIELDS:
            if item.owner is FieldOwner.METADATA and item.truncatable and item.key in metadata:
                full = encoding.value_bytes(metadata[item.key])
                metadata[item.key] = _truncation_marker(item.key, metadata[item.key], full)
                truncated.append(item.key)
        payload, size = _sealed(metadata)
    try:
        text = encoding.encode_bounded(payload, max_bytes=limit)
    except JsonOutputLimitExceeded as exc:
        raise OutputEnvelopeInvariantViolation(
            "authority-owned output exceeded the reserved envelope headroom "
            f"(needed {exc.requested_bytes} > {exc.max_bytes} bytes; "
            f"prepared {plan.prepared_bytes}, headroom {plan.headroom_bytes})",
            max_bytes=exc.max_bytes,
            requested_bytes=exc.requested_bytes,
        ) from exc
    return FinalResultEnvelope(
        payload=payload,
        text=text,
        plan=plan,
        total_bytes=size,
        truncated_metadata=tuple(truncated),
    )


__all__ = [
    "AuthorityDecisionEnvelope",
    "FIELD_BY_KEY",
    "FieldOwner",
    "FinalResultEnvelope",
    "OutputEnvelopeInvariantViolation",
    "OutputField",
    "OutputMetadata",
    "OutputPreparer",
    "PreparedPayloadStale",
    "PreparedSemanticPayload",
    "RESULT_FIELDS",
    "SerializationPlan",
    "assemble_result_payload",
    "build_final_result_envelope",
    "fields_owned_by",
    "prepare_pair_output",
    "prepared_payload_for",
    "result_payload",
]
