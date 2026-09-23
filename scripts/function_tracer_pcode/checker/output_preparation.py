# -*- coding: utf-8 -*-
"""結果の出力を authority 確定 **前** に有界に準備する（Issue #22 PR-22-D）。

順序（`authority/lifecycle/production_boundary.py` が呼ぶ）:

```text
legacy の意味解析結果
  ↓ G4-a  台帳に限界 / 内部バグ → pair 単位の結果
  ↓ G4-b  prepare_pair_output():  OutputPreparer.prepare(result, OutputOptions)
            収まる  → PreparedSemanticPayload（+ SerializationPlan、headroom 予約済み）
            超える  → raise_limitation(PAIR_TERMINAL_LIMITATION)
                      → pair 単位の UNKNOWN → その小さい結果を準備し直す
  ↓ 台帳を finalization へ（以後の限界は記録されない = 判定を変えない）
  ↓ connector.finish(...)              # 最初の不可逆な判定
  ↓ reconciliation / canonical decision / relations / conditional lane
CLI:
  build_final_result_envelope(result, seal=...)
     = A 準備済み + B authority + C 診断（残り予算まで）→ 封印 → bounded encode
```

**責務の分け方**（`RESULT_FIELDS` が field ごとに 1 行で宣言する）:

* **いつ・誰が値を決めるか**（`FieldOwner`）
  - `PREPARED`（A）: 解析・solver 由来。authority 確定前に 1 回だけ写して凍結し、
    以後は元の object を読まない。
  - `AUTHORITY`（B）: authority の attach_* が書いた値。A が同名 field を持つこと
    は無い。
  - `METADATA`（C）: 判定に関わらない観測（時間・診断・カウンタ・識別子）。
    authority 確定後に合成する。
* **収まらないときの意味**（`Overflow`）
  - `LIMITATION`: 意味の payload を表せない → pair terminal な限界（authority 前
    だけに置ける）。
  - `TRUNCATE`: 診断 → 件数 + marker に置き換える（判定を変えない）。
  - `INVARIANT`: 切り詰めてはいけない値 → 出力契約の違反（内部エラー）。
* **live object → 有界な表現の変換**: 各行の `source(result, options)` は
  **浅い view** を返す（重い leaf — 文字列・既に結果が持つ list / dict — は参照
  するだけで複製しない。費用は記録の件数に比例し、leaf の大きさに比例しない）。
  写すのは `JsonEncodingPolicy.project_bounded` だけで、残り予算に達した時点で
  写すのをやめる（巨大な値を作ってから測らない）。
* **出力 option**: `OutputOptions` を準備の時点で 1 回だけ決める（debug trace を
  添付するか・SMT 式を保存するか）。合成は `prepared.options` だけを読み、結果の
  live な flag は読まない。

依存の向き: checker → core（予算・JSON policy）/ authority（receipt の公開表現）。
意味解析・solver・renderer・identity はこの module を import しない
（`tests/unit/test_architecture_boundaries.py`）— field を足しても意味の経路は
動かない（M-3）。
"""

from __future__ import annotations

import copy
from dataclasses import dataclass
from enum import Enum
from typing import Any, Callable, Dict, List, Mapping, Optional, Tuple

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
    JsonBudgetExhausted,
    JsonEncodingPolicy,
    JsonOutputLimitExceeded,
)


#: 準備した payload の大きさを予算と比べる観測点。
PREPARATION_SITE = "checker.output_preparation.prepare"
#: 最終 envelope の大きさを確かめる観測点（authority 確定後）。
FINAL_ENVELOPE_SITE = "output.final_envelope"


class FieldOwner(str, Enum):
    """結果 JSON の field を **いつ・誰が** 決めるか。"""

    PREPARED = "prepared"    # A: authority 確定前に準備・凍結する解析由来の値
    AUTHORITY = "authority"  # B: authority の attach_* が決めた値
    METADATA = "metadata"    # C: 判定に関わらない観測（authority 確定後に合成）


class Overflow(str, Enum):
    """その field が予算に収まらないときの意味。"""

    LIMITATION = "limitation"  # 意味の payload を表せない → pair terminal な限界
    TRUNCATE = "truncate"      # 診断 → 件数 + marker（判定を変えない）
    INVARIANT = "invariant"    # 切り詰めてはいけない → 出力契約の違反（内部エラー）


#: 所有者ごとに許される超過の意味。authority 確定後に限界を作らないため、
#: `LIMITATION` を持てるのは authority 前に準備する A だけ。
_ALLOWED_OVERFLOW = {
    FieldOwner.PREPARED: frozenset({Overflow.LIMITATION, Overflow.TRUNCATE}),
    FieldOwner.AUTHORITY: frozenset({Overflow.INVARIANT}),
    FieldOwner.METADATA: frozenset({Overflow.TRUNCATE, Overflow.INVARIANT}),
}


@dataclass(frozen=True)
class OutputOptions:
    """出力の選択。準備の時点で 1 回だけ決め、以後は `prepared.options` を読む。

    どちらも判定には効かない: debug trace と SMT 式は、収まらなければ marker /
    省略になるだけで、限界にはならない。
    """

    include_debug_trace: bool = True
    include_smt_formula: bool = False

    @classmethod
    def for_result(cls, result: Any, *, save_formula: bool = False) -> "OutputOptions":
        """結果の flag（workflow が `checker.debug` から決めた値）を **ここで 1 回だけ** 読む。"""

        return cls(
            include_debug_trace=bool(getattr(result, "emit_debug_trace", True)),
            include_smt_formula=bool(save_formula),
        )


Source = Callable[[Any, OutputOptions], Tuple[bool, Any]]


@dataclass(frozen=True)
class OutputField:
    """結果 JSON の 1 field。

    `source(result, options)` は (出すか, 浅い view) を返す。view の組み立て費用は
    記録の件数に比例し、重い leaf の大きさには比例しないこと（重い leaf は参照
    するだけ）。写すのは `project_bounded` の仕事。
    """

    key: str
    owner: FieldOwner
    source: Source
    overflow: Overflow

    def __post_init__(self) -> None:
        if self.overflow not in _ALLOWED_OVERFLOW[self.owner]:
            raise ValueError(
                f"{self.key}: {self.owner.value} fields cannot overflow as "
                f"{self.overflow.value}"
            )


def _always(getter: Callable[[Any], Any]) -> Source:
    return lambda result, options: (True, getter(result))


def _when(test: Callable[[Any, OutputOptions], bool], getter: Callable[[Any], Any]) -> Source:
    return lambda result, options: (True, getter(result)) if test(result, options) else (False, None)


def _view_or_none(value: Any) -> Any:
    """`to_dict()` を持つ値の浅い view（これらの `to_dict` は参照を並べ直すだけ）。"""

    return value.to_dict() if value else None


# -- A: 解析由来の値 ----------------------------------------------------------


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
_LIMIT = Overflow.LIMITATION
_TRUNC = Overflow.TRUNCATE
_INV = Overflow.INVARIANT


def _present(attribute: str, *, truthy: bool = False) -> Callable[[Any, OutputOptions], bool]:
    if truthy:
        return lambda result, options: bool(getattr(result, attribute))
    return lambda result, options: getattr(result, attribute) is not None


#: 結果 JSON の field・所有者・超過の意味の **唯一の対応表**（並びは従来の
#: `to_dict()` の key 順）。
#:
#: 分類の規則:
#:
#: * 判定を読むのに要る解析・solver の証拠（識別子・signature・反例・solver
#:   結果・証明の provenance / evidence・gate が読む disposition）→ `_A` /
#:   `_LIMIT`。表せないなら判定を出さない。
#: * authority が決めた値 → `_B` / `_INV`（切り詰めない）。
#: * 判定に関わらない観測（時間・診断・カウンタ・経路の足跡・原因集計・debug
#:   trace）→ 切り詰めてよい（`_TRUNC`）。authority 前に写す必要がある debug
#:   trace だけ `_A`、他は authority 後に合成する `_C`。
#: * 判定に関わらないが切り詰めると結果を特定できなくなる値（content identity・
#:   総時間）→ `_C` / `_INV`。
#:
#: field を足すときはここへ 1 行足す。判定に関わらない診断なら `_C` / `_TRUNC`
#: の行を足すだけで、authority・identity・solver 側は変わらない（M-3）。
RESULT_FIELDS: Tuple[OutputField, ...] = (
    OutputField("is_equivalent", _B, _always(lambda r: r.is_equivalent), _INV),
    OutputField("function1_name", _A, _always(lambda r: r.function1_name), _LIMIT),
    OutputField("function2_name", _A, _always(lambda r: r.function2_name), _LIMIT),
    OutputField("binary1_name", _A, _always(lambda r: r.binary1_name), _LIMIT),
    OutputField("binary2_name", _A, _always(lambda r: r.binary2_name), _LIMIT),
    # content identity は `check_from_binaries` が boundary の **後** に書く
    OutputField("binary1_content_identity", _C, _always(lambda r: r.binary1_content_identity), _INV),
    OutputField("binary2_content_identity", _C, _always(lambda r: r.binary2_content_identity), _INV),
    OutputField("function1_identity", _A, _always(lambda r: r.function1_identity), _LIMIT),
    OutputField("function2_identity", _A, _always(lambda r: r.function2_identity), _LIMIT),
    OutputField(
        "function1_signature", _A, _always(lambda r: _view_or_none(r.function1_signature)), _LIMIT,
    ),
    OutputField(
        "function2_signature", _A, _always(lambda r: _view_or_none(r.function2_signature)), _LIMIT,
    ),
    OutputField(
        "effective_function1_signature", _A,
        _always(lambda r: _view_or_none(r.get_effective_function1_signature())), _LIMIT,
    ),
    OutputField(
        "effective_function2_signature", _A,
        _always(lambda r: _view_or_none(r.get_effective_function2_signature())), _LIMIT,
    ),
    OutputField(
        "function1_signature_hypotheses", _A,
        _always(lambda r: r.function1_signature_hypotheses), _LIMIT,
    ),
    OutputField(
        "function2_signature_hypotheses", _A,
        _always(lambda r: r.function2_signature_hypotheses), _LIMIT,
    ),
    OutputField("solver_results", _A, _always(lambda r: _view_or_none(r.solver_results)), _LIMIT),
    OutputField("counterexample", _A, _always(lambda r: _view_or_none(r.counterexample)), _LIMIT),
    OutputField("total_time", _C, _always(lambda r: r.total_time), _INV),
    OutputField("error_message", _B, _always(lambda r: r.error_message), _INV),
    OutputField("failure_status", _B, _always(lambda r: r.failure_status), _INV),
    OutputField("failure_message", _B, _always(lambda r: r.failure_message), _INV),
    OutputField(
        "type_fix_result", _A, _always(lambda r: _view_or_none(r.type_fix_result)), _LIMIT,
    ),
    OutputField("retry_count", _A, _always(lambda r: r.retry_count), _LIMIT),
    OutputField("is_timeout", _B, _always(lambda r: r.is_timeout()), _INV),
    OutputField("final_outcome", _B, _always(lambda r: r.final_outcome), _INV),
    OutputField("decision_receipt", _B, _always(_decision_receipt), _INV),
    OutputField("conditional_outcome", _B, _always(lambda r: r.conditional_outcome), _INV),
    OutputField(
        "conditional_decision_receipt", _B, _always(_conditional_decision_receipt), _INV,
    ),
    OutputField(
        "c_active_base", _B,
        _always(lambda r: [dict(row) for row in r.canonical_c_active_base]), _INV,
    ),
    OutputField(
        "q_open_base", _B,
        _always(lambda r: [dict(row) for row in r.canonical_q_open_base]), _INV,
    ),
    OutputField("constrained_fragments", _A, _always(lambda r: r.constrained_fragments), _LIMIT),
    # solver / pair の件数。判定には効かない観測（reporting は読むが、欠けても
    # 判定の再構成には要らない）
    OutputField("pairwise_stats", _C, _always(lambda r: r.pairwise_stats), _TRUNC),
    OutputField("pairwise_debug_stats", _C, _always(lambda r: r.pairwise_debug_stats), _TRUNC),
    OutputField(
        "unknown_reasons", _B,
        _always(lambda r: [reason.to_dict() for reason in r.unknown_reasons]), _INV,
    ),
    OutputField(
        "unknown_recovery_actions", _B,
        _always(lambda r: [action.to_dict() for action in r.unknown_recovery_actions]), _INV,
    ),
    OutputField("unknown_recovery_backlog", _B, _always(_unknown_recovery_backlog), _INV),
    OutputField(
        "decision_gated_by_pending_proof", _B,
        _always(lambda r: r.decision_gated_by_pending_proof), _INV,
    ),
    OutputField("sat_pair_info", _A, _always(lambda r: r.sat_pair_info), _LIMIT),
    # 通った phase / stage の足跡（診断）
    OutputField("stage_path", _C, _always(lambda r: r.stage_path), _TRUNC),
    OutputField("diagnostics", _C, _always(_diagnostics), _TRUNC),
    OutputField("unknown_cause_aggregate", _C, _always(_unknown_cause_aggregate), _TRUNC),
    OutputField(
        "canonical_result_finalization_bundle", _B,
        _when(
            lambda r, _o: r.canonical_result_finalization_bundle is not None,
            lambda r: dict(r.canonical_result_finalization_bundle),
        ),
        _INV,
    ),
    OutputField(
        "completed_recovery_proof_evidence", _A,
        _when(_present("completed_recovery_proof_evidence", truthy=True),
              lambda r: r.completed_recovery_proof_evidence),
        _LIMIT,
    ),
    OutputField(
        "reason_completion_applicability_contexts", _A,
        _when(_present("reason_completion_applicability_contexts", truthy=True),
              lambda r: r.reason_completion_applicability_contexts),
        _LIMIT,
    ),
    OutputField(
        "call_effect_shadow_manifest", _A,
        _when(_present("call_effect_shadow_manifest"),
              lambda r: dict(r.call_effect_shadow_manifest)),
        _LIMIT,
    ),
    OutputField(
        "call_proof_terminal_provenance", _A,
        _when(_present("call_proof_terminal_provenance"),
              lambda r: dict(r.call_proof_terminal_provenance)),
        _LIMIT,
    ),
    OutputField(
        "recurrence_promotion_receipt", _A,
        _when(_present("recurrence_promotion_receipt"),
              lambda r: dict(r.recurrence_promotion_receipt)),
        _LIMIT,
    ),
    OutputField(
        "decisive_proof_provenance", _A,
        _when(_present("decisive_proof_provenance"),
              lambda r: dict(r.decisive_proof_provenance)),
        _LIMIT,
    ),
    # soundness gate が identical-input pair の分類に読む
    OutputField(
        "identical_fast_path_disposition", _A,
        _when(_present("identical_fast_path_disposition"),
              lambda r: dict(r.identical_fast_path_disposition)),
        _LIMIT,
    ),
    OutputField(
        "identical_function_identity_evidence", _A,
        _when(_present("identical_function_identity_evidence"),
              lambda r: dict(r.identical_function_identity_evidence)),
        _LIMIT,
    ),
    OutputField(
        "mips64_abi_constraints", _A,
        _when(_present("mips64_abi_constraints", truthy=True), _mips64_abi_constraints),
        _LIMIT,
    ),
    # Issue #128 PR-128-B: trace は常に object 上に在り、debug 指定のときだけ
    # JSON へ添付する（指定は `OutputOptions` が準備時に 1 回決める）。
    # 判定に関わらないので、予算を超えるなら件数 + marker に置き換える。
    OutputField(
        "debug_trace", _A,
        _when(lambda r, o: bool(r.debug_trace) and o.include_debug_trace,
              lambda r: r.debug_trace.to_dict()),
        _TRUNC,
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
    "constrained_fragments", "sat_pair_info",
    "completed_recovery_proof_evidence", "reason_completion_applicability_contexts",
    "call_effect_shadow_manifest", "call_proof_terminal_provenance",
    "recurrence_promotion_receipt", "decisive_proof_provenance",
    "identical_fast_path_disposition", "identical_function_identity_evidence",
    "mips64_abi_constraints", "debug_trace", "smt_formula",
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
# 写しの共通部品
# ---------------------------------------------------------------------------


def _opaque_value_bytes(value: Any) -> int:
    return len(type(value).__qualname__) + 2


def _truncation_marker(key: str, view: Any, *, remaining_bytes: Optional[int]) -> Dict[str, Any]:
    """収まらなかった診断の代わりに置く値（件数 + marker）。元の値は写さない。"""

    count = len(view) if isinstance(view, (list, tuple, dict)) else None
    return {
        "truncated": True,
        "field": key,
        "reason": BudgetKind.SERIALIZATION_BYTES.value,
        "exceeded_bytes": remaining_bytes,
        "original_items": count,
    }


class _Accumulator:
    """1 つの JSON object へ field を順に足していく勘定（key・区切りを含む）。"""

    def __init__(self, encoding: JsonEncodingPolicy, limit: Optional[int], used: int = 0) -> None:
        self.encoding = encoding
        self.limit = limit
        self.used = used

    def overhead(self, key: str) -> int:
        encoding = self.encoding
        return (
            encoding.string_bytes(key)
            + len(encoding.key_separator.encode("utf-8"))
            + len(encoding.item_separator.encode("utf-8"))
        )

    def remaining_for(self, key: str) -> Optional[int]:
        if self.limit is None:
            return None
        return self.limit - self.used - self.overhead(key)

    def project(self, key: str, view: Any) -> Tuple[Any, int]:
        """`view` を残り予算まで写す（収まらなければ `JsonBudgetExhausted`）。"""

        remaining = self.remaining_for(key)
        if remaining is not None and remaining < 0:
            raise JsonBudgetExhausted(consumed_bytes=0, max_bytes=remaining)
        value, size = self.encoding.project_bounded(
            view, max_bytes=remaining, opaque_bytes=_opaque_value_bytes,
        )
        return value, self.overhead(key) + size

    def commit(self, size: int) -> None:
        self.used += size


def _project_or_mark(
    accumulator: _Accumulator, item: OutputField, view: Any,
) -> Tuple[Optional[Tuple[Any, int]], str]:
    """切り詰めてよい field を写す。収まらなければ marker、marker も入らなければ省く。"""

    try:
        return accumulator.project(item.key, view), "json"
    except JsonBudgetExhausted:
        pass
    marker = _truncation_marker(
        item.key, view, remaining_bytes=accumulator.remaining_for(item.key),
    )
    try:
        return accumulator.project(item.key, marker), "truncation_marker"
    except JsonBudgetExhausted:
        return None, "omitted"


# ---------------------------------------------------------------------------
# A: 準備
# ---------------------------------------------------------------------------


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
    #: field ごとの (key, byte 数, 表現)。表現は `json` / `truncation_marker` / `omitted`
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
class PreparedArtifact:
    """JSON の外へ出す準備済みの成果物（`--save-formula` の SMT 式）。

    判定には効かない出力の選択なので、収まらなければ **省く**（限界にしない）。
    """

    text: Optional[str]
    #: 省いたときの上限（省いていなければ `None`）
    omitted_over_bytes: Optional[int] = None


@dataclass(frozen=True)
class PreparedSemanticPayload:
    """authority 確定前に作る解析由来の payload（A）。作った後は元の object を読まない。

    **canonical な判定も canonical reason も持たない**。legacy の reason は
    `raw_limitation_evidence`（reason id と stage）として残すだけ。
    """

    fields: Tuple[Tuple[str, Any], ...]
    raw_limitation_evidence: Tuple[Tuple[str, Optional[str]], ...]
    plan: SerializationPlan
    options: OutputOptions
    smt_formula: PreparedArtifact = PreparedArtifact(None)
    #: 準備に使った属性値（差し替え検出用。判定にも出力にも使わない）
    _sources: Tuple[Tuple[str, Any], ...] = ()

    def keys(self) -> Tuple[str, ...]:
        return tuple(key for key, _value in self.fields)

    def values_for_output(self) -> Dict[str, Any]:
        """出力へ置く値の **複製**（呼び出し側が壊しても準備済みの値は変わらない）。

        複製するのは既に予算内に収めた値だけ。
        """

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


def _bounded_utf8_length(text: str, max_bytes: Optional[int]) -> int:
    """`text` の UTF-8 byte 数（`max_bytes` を超えた時点で `max_bytes + 1`）。"""

    from scripts.function_tracer_pcode.core.render_output import utf8_length

    if max_bytes is not None and len(text) > max_bytes:
        return max_bytes + 1
    total = 0
    step = 1 << 16
    for start in range(0, len(text), step):
        total += utf8_length(text[start:start + step])
        if max_bytes is not None and total > max_bytes:
            return max_bytes + 1
    return total


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

    def prepare(self, result: Any, options: Optional[OutputOptions] = None) -> PreparedSemanticPayload:
        """A を残り予算まで写して凍結する。意味の field が収まらなければ限界にする。

        意味の field（`LIMITATION`）を先に、診断（`TRUNCATE`）を残りで写す。
        どちらも `project_bounded` が予算に達した時点で写すのをやめるので、
        巨大な値を作ってから測ることはない。
        """

        if options is None:
            options = OutputOptions.for_result(result)
        accumulator = _Accumulator(self.encoding, self.policy.prepared_payload_limit())
        values: List[Tuple[str, Any]] = []
        sizes: List[Tuple[str, int, str]] = []
        prepared_rows = [item for item in RESULT_FIELDS if item.owner is FieldOwner.PREPARED]
        ordered = (
            [item for item in prepared_rows if item.overflow is Overflow.LIMITATION]
            + [item for item in prepared_rows if item.overflow is Overflow.TRUNCATE]
        )
        for item in ordered:
            present, view = item.source(result, options)
            if not present:
                continue
            if item.overflow is Overflow.LIMITATION:
                try:
                    value, size = accumulator.project(item.key, view)
                except JsonBudgetExhausted as exc:
                    self._raise_exceeded(accumulator, item.key, exc, sizes)
                shape = "json"
            else:
                projected, shape = _project_or_mark(accumulator, item, view)
                if projected is None:
                    sizes.append((item.key, 0, shape))
                    continue
                value, size = projected
            accumulator.commit(size)
            sizes.append((item.key, size, shape))
            values.append((item.key, value))
        order = {item.key: index for index, item in enumerate(RESULT_FIELDS)}
        values.sort(key=lambda row: order[row[0]])
        plan = SerializationPlan(
            encoding=self.encoding,
            max_bytes=self.policy.serialization_bytes,
            headroom_bytes=self.policy.envelope_headroom_bytes,
            prepared_bytes=accumulator.used,
            field_bytes=tuple(sizes),
        )
        observe_budget_usage(
            BudgetKind.SERIALIZATION_BYTES,
            accumulator.used + self.policy.envelope_headroom_bytes,
            site=PREPARATION_SITE,
        )
        return PreparedSemanticPayload(
            fields=tuple(values),
            raw_limitation_evidence=tuple(
                (reason.reason_id, getattr(reason, "stage", None))
                for reason in (getattr(result, "unknown_reasons", None) or ())
            ),
            plan=plan,
            options=options,
            smt_formula=self._prepare_smt_formula(result, options),
            _sources=tuple(
                (name, getattr(result, name, None))
                for name in _PREPARED_SOURCE_ATTRIBUTES
            ),
        )

    def _prepare_smt_formula(self, result: Any, options: OutputOptions) -> PreparedArtifact:
        """保存を頼まれた SMT 式を、直列化 1 つ分の予算まで準備する（超えたら省く）。"""

        text = getattr(result, "smt_formula", None)
        if not options.include_smt_formula or not text:
            return PreparedArtifact(None)
        limit = self.policy.serialization_bytes
        if limit is not None and _bounded_utf8_length(text, limit) > limit:
            return PreparedArtifact(None, omitted_over_bytes=limit)
        return PreparedArtifact(text)

    def _raise_exceeded(
        self,
        accumulator: _Accumulator,
        key: str,
        exc: JsonBudgetExhausted,
        sizes: List[Tuple[str, int, str]],
    ) -> None:
        observed = (
            max(accumulator.used + exc.consumed_bytes, (accumulator.limit or 0) + 1)
            + self.policy.envelope_headroom_bytes
        )
        raise_expression_size_budget_exceeded(
            BudgetKind.SERIALIZATION_BYTES,
            observed=observed,
            limit=self.policy.serialization_bytes,
            site=PREPARATION_SITE,
            target_key=("result_payload", key),
            evidence=(
                f"prepared_bytes_before={accumulator.used}",
                f"headroom_bytes={self.policy.envelope_headroom_bytes}",
                f"exceeding_field={key}",
                f"fields_before={len(sizes)}",
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
    save_formula: bool = False,
) -> Any:
    """G4-b: authority 確定前に出力を準備する（収まらなければ pair 単位の限界）。

    出力 option はここで 1 回だけ決める（`OutputOptions.for_result`）。

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
    options = OutputOptions.for_result(result, save_formula=save_formula)
    try:
        prepared = preparer.prepare(result, options)
    except AnalysisLimitation:
        result = apply_pair_failure_gate(
            checker,
            result,
            function_name1=function_name1,
            function_name2=function_name2,
            start_time=start_time,
        )
        try:
            prepared = preparer.prepare(result, options)
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
            prepared = OutputPreparer(BudgetPolicy.unlimited()).prepare(result, options)
    _attach_budget_diagnostics(result, prepared, policy)
    result.prepared_semantic_payload = prepared
    return result


# ---------------------------------------------------------------------------
# B / C と合成
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class AuthorityDecisionEnvelope:
    """authority が確定した field（B）。authority の attach_* が書いた値だけを読む。

    authority の値は authority が作った時点で既に在る（ここで作り直さない）ので、
    写さずにそのまま置く。大きさは最終 envelope が測る（切り詰めない）。
    """

    fields: Tuple[Tuple[str, Any], ...]

    @classmethod
    def from_result(cls, result: Any, options: OutputOptions) -> "AuthorityDecisionEnvelope":
        return cls(tuple(_views(result, options, FieldOwner.AUTHORITY)))


@dataclass(frozen=True)
class OutputMetadata:
    """判定に関わらない field（C）の、合成に使う値。"""

    fields: Tuple[Tuple[str, Any], ...]


def _views(result: Any, options: OutputOptions, owner: FieldOwner):
    for item in RESULT_FIELDS:
        if item.owner is not owner:
            continue
        present, view = item.source(result, options)
        if present:
            yield item.key, view


def _metadata_unbounded(result: Any, options: OutputOptions) -> OutputMetadata:
    return OutputMetadata(tuple(_views(result, options, FieldOwner.METADATA)))


def _metadata_bounded(
    result: Any, options: OutputOptions, accumulator: _Accumulator,
) -> Tuple[OutputMetadata, Tuple[str, ...]]:
    """C を残り予算まで写す。切り詰めてよい field は marker、いけない field は違反。"""

    rows: List[Tuple[str, Any]] = []
    truncated: List[str] = []
    metadata_rows = [item for item in RESULT_FIELDS if item.owner is FieldOwner.METADATA]
    ordered = (
        [item for item in metadata_rows if item.overflow is Overflow.INVARIANT]
        + [item for item in metadata_rows if item.overflow is Overflow.TRUNCATE]
    )
    for item in ordered:
        present, view = item.source(result, options)
        if not present:
            continue
        if item.overflow is Overflow.INVARIANT:
            try:
                value, size = accumulator.project(item.key, view)
            except JsonBudgetExhausted as exc:
                raise OutputEnvelopeInvariantViolation(
                    f"{item.key} must not be truncated but does not fit the envelope",
                    max_bytes=accumulator.limit or 0,
                    requested_bytes=accumulator.used + exc.consumed_bytes,
                ) from exc
            shape = "json"
        else:
            projected, shape = _project_or_mark(accumulator, item, view)
            if projected is None:
                truncated.append(item.key)
                continue
            value, size = projected
        if shape != "json":
            truncated.append(item.key)
        accumulator.commit(size)
        rows.append((item.key, value))
    return OutputMetadata(tuple(rows)), tuple(truncated)


def assemble_result_payload(
    prepared: PreparedSemanticPayload,
    authority: AuthorityDecisionEnvelope,
    metadata: OutputMetadata,
) -> Dict[str, Any]:
    """A + B + C を従来の key 順で 1 つの dict にする（大きさは見ない）。

    同じ key を 2 つの層が持つことは無い（`RESULT_FIELDS` が所有者を 1 つに
    決めている）。念のため重なりは内部エラーにする — B を A で上書きする経路を
    作らないため。
    """

    parts: Dict[str, Any] = {}
    for layer in (prepared.values_for_output(), dict(authority.fields), dict(metadata.fields)):
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


def prepared_smt_formula(result: Any) -> PreparedArtifact:
    """`--save-formula` が書く SMT 式（準備済みの成果物だけを返す）。"""

    prepared = getattr(result, "prepared_semantic_payload", None)
    if prepared is None:
        return PreparedArtifact(getattr(result, "smt_formula", None))
    return prepared.smt_formula


def result_payload(result: Any) -> Dict[str, Any]:
    """`EquivalenceResult.to_dict()` の本体（A は準備済みの値、B / C は今の値）。

    上限は掛けない（上限付きで書くのは `build_final_result_envelope`）。
    """

    prepared = prepared_payload_for(result)
    return assemble_result_payload(
        prepared,
        AuthorityDecisionEnvelope.from_result(result, prepared.options),
        _metadata_unbounded(result, prepared.options),
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

    上限は準備したときの plan（authority 確定前に決めた値）。A は準備済み、B は
    authority が作った値をそのまま置き、C だけを残り予算まで写す（切り詰めて
    よい field は marker）。封印（bundle）は preimage 全体の digest を持つので、
    封印の後で payload を変えない — bundle の大きさは封印してみないと分からない
    ため、収まらなかったときだけ bundle の分を空けて C を写し直し、封印し直す。
    B は切り詰めない。それでも超えるなら `OutputEnvelopeInvariantViolation`。
    """

    prepared = prepared_payload_for(result)
    plan = prepared.plan
    options = prepared.options
    encoding = plan.encoding
    limit = plan.max_bytes
    authority = AuthorityDecisionEnvelope.from_result(result, options)
    base = assemble_result_payload(prepared, authority, OutputMetadata(()))
    base_bytes = encoding.value_bytes(base, max_bytes=limit)
    if limit is not None and base_bytes > limit:
        raise OutputEnvelopeInvariantViolation(
            "prepared and authority-owned output exceeded the envelope before metadata "
            f"({base_bytes} > {limit} bytes; prepared {plan.prepared_bytes}, "
            f"headroom {plan.headroom_bytes})",
            max_bytes=limit,
            requested_bytes=base_bytes,
        )

    def _compose(reserve: int):
        accumulator = _Accumulator(encoding, limit, used=base_bytes + reserve)
        metadata, truncated = _metadata_bounded(result, options, accumulator)
        preimage = assemble_result_payload(prepared, authority, metadata)
        payload = dict(preimage)
        if seal is not None:
            payload["canonical_result_finalization_bundle"] = dict(seal(preimage))
        return payload, truncated, encoding.value_bytes(payload, max_bytes=limit)

    payload, truncated, size = _compose(0)
    if limit is not None and size > limit and seal is not None:
        bundle = payload["canonical_result_finalization_bundle"]
        reserve = _Accumulator(encoding, None).overhead(
            "canonical_result_finalization_bundle"
        ) + encoding.value_bytes(bundle)
        payload, truncated, size = _compose(reserve)
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
        truncated_metadata=truncated,
    )


__all__ = [
    "AuthorityDecisionEnvelope",
    "FIELD_BY_KEY",
    "FieldOwner",
    "FinalResultEnvelope",
    "OutputEnvelopeInvariantViolation",
    "OutputField",
    "OutputMetadata",
    "OutputOptions",
    "OutputPreparer",
    "Overflow",
    "PreparedArtifact",
    "PreparedPayloadStale",
    "PreparedSemanticPayload",
    "RESULT_FIELDS",
    "SerializationPlan",
    "assemble_result_payload",
    "build_final_result_envelope",
    "fields_owned_by",
    "prepare_pair_output",
    "prepared_payload_for",
    "prepared_smt_formula",
    "result_payload",
]
