# -*- coding: utf-8 -*-
"""結果の出力を authority 確定 **前** に有界に準備する（Issue #22 PR-22-D）。

中心の契約:

> authority へ進む前に、live な解析・結果 object から、有界で JSON にでき、以後
> live object を読み直さない immutable な prepared representation への変換を
> 完了する。

順序（`authority/lifecycle/production_boundary.py` が呼ぶ）:

```text
legacy の意味解析結果
  ↓ G4-a  台帳に限界 / 内部バグ → pair 単位の結果
  ↓ G4-b  prepare_pair_output():  OutputPreparer.prepare(result, OutputOptions)
            収まる     → PreparedSemanticPayload（canonical JSON の field だけ）
            超える     → raise_limitation(PAIR_TERMINAL_LIMITATION)
                         → pair 単位の UNKNOWN → その小さい結果を準備し直す
            JSON でない → 内部エラー（producer のバグ）→ ERROR の結果を準備し直す
  ↓ connector.finish(...)              # 最初の不可逆な判定
  ↓ reconciliation / canonical decision / relations / conditional lane
CLI:
  build_final_result_envelope(result, seal=...)
     = A 準備済み + B authority + C 診断（残り予算まで）→ 封印 → bounded encode
```

**field の宣言**（`RESULT_FIELDS` が 1 field 1 行）:

* **いつ・誰が値を決めるか**（`FieldOwner`）: `PREPARED`（A、authority 確定前に
  1 回だけ準備）/ `AUTHORITY`（B、authority の attach_* が書いた値）/ `METADATA`
  （C、判定に関わらない観測。authority 確定後に合成）。
* **収まらないときの意味**（`Overflow`）: `LIMITATION`（意味の payload を表せない →
  pair terminal な限界。authority 前の A だけ）/ `TRUNCATE`（診断 → 件数 + marker）/
  `INVARIANT`（切り詰めてはいけない → 出力契約の違反 = 内部エラー）。
* **live object の読み方**（`read(result, options)`）: 値そのものではなく
  **JSON source**（`core/json_encoding` の文法）を返す。既存の container は参照を
  渡し、record は record 自身を渡し（walker がその `json_items()` を引く）、
  collection の並べ直しは `each` / `pairs_of` などの source で渡す。`to_dict()` の
  呼び出し・複製・内包表記で表現を先に作らない（`tests/unit/test_architecture_boundaries.py`
  が AST で固定）。表現を作るのは `OutputField.prepare` が呼ぶ `JsonEncodingPolicy.prepare`
  の walker だけで、それは要素を引き出すたびに数え、残り予算に達した時点で止まる。

**出力 option**: `OutputOptions` を準備の時点で 1 回だけ決める（debug trace を添付
するか・SMT 式を保存するか）。合成は `prepared.options` だけを読む。

**authority 確定後**: A は作り直さない（準備済みの複製を置く）。B は authority の
値、C は結果の観測。どちらも同じ `JsonEncodingPolicy.prepare` を通して canonical に
し、object 全体の勘定は `JsonObjectBudget`（policy が framing を決める）1 つで持つ。

依存の向き: checker → core（予算・JSON policy）/ authority（receipt の公開表現）。
意味解析・solver・renderer・identity はこの module を import しない
（`tests/unit/test_architecture_boundaries.py`）— field を足しても意味の経路は
動かない（M-3）。
"""

from __future__ import annotations

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
    JsonBudget,
    JsonBudgetExhausted,
    JsonEncodingPolicy,
    JsonObjectBudget,
    JsonOutputLimitExceeded,
    JsonValueRejected,
    PreparedJson,
    each,
    inline,
    is_prepared_json,
    pairs_of,
    text,
)


#: 準備した payload の大きさを予算と比べる観測点。
PREPARATION_SITE = "checker.output_preparation.prepare"
#: 原因集計の trace 由来の部分を準備する観測点（authority 確定前、診断）。
CAUSE_EVIDENCE_SITE = "checker.output_preparation.cause_evidence"
#: 最終 envelope の大きさを確かめる観測点（authority 確定後）。
FINAL_ENVELOPE_SITE = "output.final_envelope"
#: 封印（finalization bundle）の key。封印は preimage 全体の digest を持つので最後に足す。
BUNDLE_KEY = "canonical_result_finalization_bundle"


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


class _Absent:
    __slots__ = ()

    def __repr__(self) -> str:  # pragma: no cover - debug 表示
        return "ABSENT"


#: `read` が「この field を出さない」ときに返す値。
ABSENT = _Absent()

#: `read(result, options)` → JSON source か `ABSENT`。
Read = Callable[[Any, OutputOptions], Any]


@dataclass(frozen=True)
class PreparedField:
    """準備した 1 field。値は `PreparedJson`（canonical・byte 数つき）だけ。"""

    key: str
    json: Optional[PreparedJson]
    #: `json` / `truncation_marker` / `omitted`
    shape: str

    def __post_init__(self) -> None:
        if self.shape not in ("json", "truncation_marker", "omitted"):
            raise ValueError(f"unknown prepared field shape {self.shape!r}")
        if (self.json is None) != (self.shape == "omitted"):
            raise TypeError(f"{self.key}: only an omitted field lacks its prepared JSON")
        if self.json is not None and not is_prepared_json(self.json):
            raise TypeError(
                f"{self.key}: a prepared field holds only JsonEncodingPolicy.prepare output"
            )

    @property
    def encoded_bytes(self) -> int:
        return 0 if self.json is None else self.json.encoded_bytes


@dataclass
class PreparationContext:
    """1 つの JSON object を準備する間の勘定（option と、policy が数える framing）。"""

    options: OutputOptions
    members: JsonObjectBudget

    @property
    def encoding(self) -> JsonEncodingPolicy:
        return self.members.policy


def _truncation_marker(
    key: str,
    source: Any,
    *,
    remaining_bytes: Optional[int],
    rejected: Optional[JsonValueRejected] = None,
) -> Dict[str, Any]:
    """表せなかった診断の代わりに置く値（件数 + marker）。元の値は写さない。

    予算に収まらない（`serialization_bytes`）か、JSON にならない値を含む
    （`not_json`、どこで拒んだかを短く残す）。どちらも判定には関わらない。
    """

    count = len(source) if isinstance(source, (list, tuple, Mapping)) else None
    marker: Dict[str, Any] = {
        "truncated": True,
        "field": key,
        "reason": BudgetKind.SERIALIZATION_BYTES.value if rejected is None else "not_json",
        "exceeded_bytes": remaining_bytes,
        "original_items": count,
    }
    if rejected is not None:
        from scripts.function_tracer_pcode.checker.output_schema import MARKER_PATH_MAX_CHARS

        marker["rejected_at"] = str(rejected.path)[:MARKER_PATH_MAX_CHARS]
    return marker


def _prepare_member(
    context: PreparationContext,
    key: str,
    source: Any,
    overflow: Overflow,
    *,
    field_max_bytes: Optional[int] = None,
) -> PreparedField:
    """`source` を object の次の member として、残り予算まで準備する。

    `LIMITATION` / `INVARIANT` の field が収まらなければ `JsonBudgetExhausted`、
    JSON source でなければ `JsonValueRejected` をそのまま上げる（意味づけは呼ぶ側）。
    `TRUNCATE` の field はどちらでも marker（marker も入らなければ省く）。
    """

    members = context.members
    encoding = context.encoding
    remaining = members.remaining_for(key)
    if field_max_bytes is not None:
        # 出力 schema の上限（B）: headroom が余っていても、それを超える値は違反
        remaining = field_max_bytes if remaining is None else min(remaining, field_max_bytes)
    rejected: Optional[JsonValueRejected] = None
    try:
        if remaining is not None and remaining < 0:
            raise JsonBudgetExhausted(consumed_bytes=0, max_bytes=remaining)
        prepared = encoding.prepare(source, max_bytes=remaining)
        shape = "json"
    except (JsonBudgetExhausted, JsonValueRejected) as exc:
        # 切り詰めてよい診断は、収まらなくても JSON にならなくても marker にする
        # （診断の欠陥で判定を変えない）。それ以外の意味づけは呼ぶ側。
        if overflow is not Overflow.TRUNCATE:
            raise
        if isinstance(exc, JsonValueRejected):
            rejected = exc
        marker = _truncation_marker(key, source, remaining_bytes=remaining, rejected=rejected)
        try:
            if remaining is not None and remaining < 0:
                raise JsonBudgetExhausted(consumed_bytes=0, max_bytes=remaining)
            prepared = encoding.prepare(marker, max_bytes=remaining)
        except JsonBudgetExhausted:
            return PreparedField(key, None, "omitted")
        shape = "truncation_marker"
    members.add(key, prepared.encoded_bytes)
    return PreparedField(key, prepared, shape)


@dataclass(frozen=True)
class OutputField:
    """結果 JSON の 1 field（**安定 interface**）。

    `read(result, options)` は JSON source（または `ABSENT`）を返すだけで、表現を
    作らない。表現を作るのは `prepare` だけで、それは `context` の残り予算までしか
    辿らない — producer が予算を知らずに巨大な値を作る経路は無い。
    """

    key: str
    owner: FieldOwner
    read: Read
    overflow: Overflow

    def __post_init__(self) -> None:
        if self.overflow not in _ALLOWED_OVERFLOW[self.owner]:
            raise ValueError(
                f"{self.key}: {self.owner.value} fields cannot overflow as "
                f"{self.overflow.value}"
            )

    def prepare(
        self,
        result: Any,
        context: PreparationContext,
        *,
        field_max_bytes: Optional[int] = None,
    ) -> Optional[PreparedField]:
        """この field を `context` の object の次の member として準備する（出さないなら `None`）。

        `field_max_bytes` は出力 schema がこの field に許す上限（B の field）。
        """

        source = self.read(result, context.options)
        if source is ABSENT:
            return None
        return _prepare_member(
            context, self.key, source, self.overflow, field_max_bytes=field_max_bytes,
        )


# ---------------------------------------------------------------------------
# field の読み方（JSON source を返すだけ。表現は作らない）
# ---------------------------------------------------------------------------


def _when_truthy(attribute: str) -> Read:
    def read(r, _o):
        value = getattr(r, attribute)
        return value if value else ABSENT
    return read


def _when_present(attribute: str) -> Read:
    def read(r, _o):
        value = getattr(r, attribute)
        return ABSENT if value is None else value
    return read


def _mips64_abi_constraints(r, _o) -> Any:
    constraints = r.mips64_abi_constraints
    if not constraints:
        return ABSENT
    return pairs_of(
        (key, inline(("signedness", value[0]), ("narrow_bits", value[1])))
        for key, value in constraints.items()
    )


def _message(attribute: str) -> Read:
    """失敗の自由文（出力 schema の文字数まで。超えた分は明示の marker）。"""

    def read(r, _o):
        from scripts.function_tracer_pcode.checker.output_schema import MESSAGE_MAX_CHARS

        return text(getattr(r, attribute), MESSAGE_MAX_CHARS)
    return read


def _debug_trace(r, o) -> Any:
    # Issue #128 PR-128-B: trace は常に object 上に在り、debug 指定のときだけ JSON へ
    # 添付する（指定は `OutputOptions` が準備時に 1 回決める）。
    trace = r.debug_trace
    if trace and o.include_debug_trace:
        return trace
    return ABSENT


def _decision_receipt(r, _o) -> Any:
    if r.decision_receipt is not None:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            decision_receipt_payload,
            outcome_from_result,
        )

        outcome_from_result(r)
        return decision_receipt_payload(r.decision_receipt)
    if r.canonical_decision_required:
        raise ValueError("canonical serialization lacks DecisionReceipt")
    return None


def _conditional_decision_receipt(r, _o) -> Any:
    if r.conditional_decision_receipt is not None:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            conditional_decision_receipt_payload,
        )

        return conditional_decision_receipt_payload(r.conditional_decision_receipt)
    if r.conditional_outcome is not None:
        raise ValueError("conditional outcome without its ConditionalDecisionReceipt")
    return None


def _unknown_recovery_backlog(r, _o) -> Any:
    from scripts.function_tracer_pcode.checker.unknown_reason import recovery_backlog_source

    return recovery_backlog_source(r.unknown_reasons)


def _diagnostics(r, _o) -> Any:
    from scripts.function_tracer_pcode.checker.diagnostics import result_diagnostics_payload

    return result_diagnostics_payload(r, lazy=True)


def _unknown_cause_aggregate(r, _o) -> Any:
    # Issue #128: 原因分析の compact 集計は常時出す。CLI が封印の前に確定させる
    # （`attach_cause_aggregate`）。確定していなければその場で作る。どちらも trace 由来の
    # 部分は authority 前に準備した値（`PreparedSemanticPayload.cause_evidence`）を読み、
    # authority 後に live な trace を辿らない（残りは canonical reason だけ）。
    if r.unknown_cause_aggregate is not None:
        return r.unknown_cause_aggregate
    from scripts.function_tracer_pcode.checker.cause_aggregate import (
        build_unknown_cause_aggregate,
    )

    return build_unknown_cause_aggregate(r)


_A = FieldOwner.PREPARED
_B = FieldOwner.AUTHORITY
_C = FieldOwner.METADATA
_LIMIT = Overflow.LIMITATION
_TRUNC = Overflow.TRUNCATE
_INV = Overflow.INVARIANT


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
#: field を足すときはここへ 1 行足す。判定に関わらない診断（`_C` / `_TRUNC`）はこの
#: 1 行だけ（headroom は marker の分を自動で予約する）。B の field と切り詰めない C の
#: field は、上限を `checker/output_schema.py` に 1 行足す。authority・identity・solver
#: 側は変わらない（M-3）。
RESULT_FIELDS: Tuple[OutputField, ...] = (
    OutputField("is_equivalent", _B, lambda r, _o: r.is_equivalent, _INV),
    OutputField("function1_name", _A, lambda r, _o: r.function1_name, _LIMIT),
    OutputField("function2_name", _A, lambda r, _o: r.function2_name, _LIMIT),
    OutputField("binary1_name", _A, lambda r, _o: r.binary1_name, _LIMIT),
    OutputField("binary2_name", _A, lambda r, _o: r.binary2_name, _LIMIT),
    # content identity は `check_from_binaries` が boundary の **後** に書く
    OutputField("binary1_content_identity", _C, lambda r, _o: r.binary1_content_identity, _INV),
    OutputField("binary2_content_identity", _C, lambda r, _o: r.binary2_content_identity, _INV),
    OutputField("function1_identity", _A, lambda r, _o: r.function1_identity, _LIMIT),
    OutputField("function2_identity", _A, lambda r, _o: r.function2_identity, _LIMIT),
    OutputField("function1_signature", _A, lambda r, _o: r.function1_signature, _LIMIT),
    OutputField("function2_signature", _A, lambda r, _o: r.function2_signature, _LIMIT),
    OutputField(
        "effective_function1_signature", _A,
        lambda r, _o: r.get_effective_function1_signature(), _LIMIT,
    ),
    OutputField(
        "effective_function2_signature", _A,
        lambda r, _o: r.get_effective_function2_signature(), _LIMIT,
    ),
    OutputField(
        "function1_signature_hypotheses", _A,
        lambda r, _o: r.function1_signature_hypotheses, _LIMIT,
    ),
    OutputField(
        "function2_signature_hypotheses", _A,
        lambda r, _o: r.function2_signature_hypotheses, _LIMIT,
    ),
    OutputField("solver_results", _A, lambda r, _o: r.solver_results or None, _LIMIT),
    OutputField("counterexample", _A, lambda r, _o: r.counterexample, _LIMIT),
    OutputField("total_time", _C, lambda r, _o: r.total_time, _INV),
    OutputField("error_message", _B, _message("error_message"), _INV),
    OutputField("failure_status", _B, lambda r, _o: r.failure_status, _INV),
    OutputField("failure_message", _B, _message("failure_message"), _INV),
    OutputField("type_fix_result", _A, lambda r, _o: r.type_fix_result, _LIMIT),
    OutputField("retry_count", _A, lambda r, _o: r.retry_count, _LIMIT),
    OutputField("is_timeout", _B, lambda r, _o: r.is_timeout(), _INV),
    OutputField("final_outcome", _B, lambda r, _o: r.final_outcome, _INV),
    OutputField("decision_receipt", _B, _decision_receipt, _INV),
    OutputField("conditional_outcome", _B, lambda r, _o: r.conditional_outcome, _INV),
    OutputField("conditional_decision_receipt", _B, _conditional_decision_receipt, _INV),
    OutputField("c_active_base", _B, lambda r, _o: r.canonical_c_active_base, _INV),
    OutputField("q_open_base", _B, lambda r, _o: r.canonical_q_open_base, _INV),
    OutputField("constrained_fragments", _A, lambda r, _o: r.constrained_fragments, _LIMIT),
    # solver / pair の件数。判定には効かない観測（reporting は読むが、欠けても
    # 判定の再構成には要らない）
    OutputField("pairwise_stats", _C, lambda r, _o: r.pairwise_stats, _TRUNC),
    OutputField("pairwise_debug_stats", _C, lambda r, _o: r.pairwise_debug_stats, _TRUNC),
    OutputField("unknown_reasons", _B, lambda r, _o: each(r.unknown_reasons), _INV),
    OutputField(
        "unknown_recovery_actions", _B,
        lambda r, _o: each(r.unknown_recovery_actions), _INV,
    ),
    OutputField("unknown_recovery_backlog", _B, _unknown_recovery_backlog, _INV),
    OutputField(
        "decision_gated_by_pending_proof", _B,
        lambda r, _o: r.decision_gated_by_pending_proof, _INV,
    ),
    OutputField("sat_pair_info", _A, lambda r, _o: r.sat_pair_info, _LIMIT),
    # 通った phase / stage の足跡（診断）
    OutputField("stage_path", _C, lambda r, _o: r.stage_path, _TRUNC),
    OutputField("diagnostics", _C, _diagnostics, _TRUNC),
    OutputField("unknown_cause_aggregate", _C, _unknown_cause_aggregate, _TRUNC),
    OutputField(BUNDLE_KEY, _B, _when_present(BUNDLE_KEY), _INV),
    # 出力の契約違反で ERROR にした結果だけが持つ: 取って代わられた判定の receipt
    OutputField("superseded_decision_receipt", _B, _when_present("superseded_decision_receipt"), _INV),
    OutputField(
        "completed_recovery_proof_evidence", _A,
        _when_truthy("completed_recovery_proof_evidence"), _LIMIT,
    ),
    OutputField(
        "reason_completion_applicability_contexts", _A,
        _when_truthy("reason_completion_applicability_contexts"), _LIMIT,
    ),
    OutputField(
        "call_effect_shadow_manifest", _A,
        _when_present("call_effect_shadow_manifest"), _LIMIT,
    ),
    OutputField(
        "call_proof_terminal_provenance", _A,
        _when_present("call_proof_terminal_provenance"), _LIMIT,
    ),
    OutputField(
        "recurrence_promotion_receipt", _A,
        _when_present("recurrence_promotion_receipt"), _LIMIT,
    ),
    OutputField(
        "decisive_proof_provenance", _A,
        _when_present("decisive_proof_provenance"), _LIMIT,
    ),
    # soundness gate が identical-input pair の分類に読む
    OutputField(
        "identical_fast_path_disposition", _A,
        _when_present("identical_fast_path_disposition"), _LIMIT,
    ),
    OutputField(
        "identical_function_identity_evidence", _A,
        _when_present("identical_function_identity_evidence"), _LIMIT,
    ),
    OutputField("mips64_abi_constraints", _A, _mips64_abi_constraints, _LIMIT),
    # 判定に関わらないので、予算を超えるなら件数 + marker に置き換える。
    OutputField("debug_trace", _A, _debug_trace, _TRUNC),
)

FIELD_BY_KEY: Dict[str, OutputField] = {item.key: item for item in RESULT_FIELDS}


def _field_order() -> Dict[str, int]:
    """今の `RESULT_FIELDS` の並び（出力の key 順）。"""

    return {item.key: index for index, item in enumerate(RESULT_FIELDS)}

#: A の field が読む結果の属性。準備の後にこれらを **差し替える** のは内部バグ
#: （準備済みの値が結果を表さなくなる）で、`EquivalenceResult.__setattr__` が拒む。
#: 読み方と一致していることは architecture test が AST で確かめる。
PREPARED_SOURCE_ATTRIBUTES = frozenset({
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
})


def fields_owned_by(owner: FieldOwner) -> Tuple[str, ...]:
    return tuple(item.key for item in RESULT_FIELDS if item.owner is owner)


class PreparedPayloadStale(AnalysisFailureError):
    """準備した後で A の元になる属性を差し替えようとした（内部バグ）。"""


class OutputEnvelopeInvariantViolation(AnalysisFailureError):
    """authority 確定後の field が予約した headroom に収まらない / JSON にならない。

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


@dataclass(frozen=True)
class SerializationPlan:
    """準備した payload の大きさと予約の内訳（診断に出す、判定には使わない）。"""

    encoding: JsonEncodingPolicy
    #: 結果 JSON 全体の上限（`None` は無制限）
    max_bytes: Optional[int]
    #: authority 確定後の field のために空けた byte 数
    headroom_bytes: int
    #: A の field だけで閉じた object の byte 数（framing は policy が数えた値）
    prepared_bytes: int
    #: field ごとの (key, 値の byte 数, 表現)。表現は `json` / `truncation_marker` / `omitted`
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

    def __post_init__(self) -> None:
        if self.text is not None and type(self.text) is not str:
            raise TypeError("a prepared artifact holds only an exact str")


@dataclass(frozen=True)
class PreparedSemanticPayload:
    """authority 確定前に作る解析由来の payload（A）。

    **型の契約**（`__post_init__` が作成時に確かめる）: field は
    `JsonEncodingPolicy.prepare` が作った `PreparedJson` だけ（canonical な JSON・
    有界・live object と独立・書き出しに変換が要らない）。任意の object は入れられ
    ない。canonical な判定も canonical reason も持たない — legacy の reason は
    `raw_limitation_evidence`（reason id と stage の文字列）として残すだけ。
    """

    fields: Tuple[PreparedField, ...]
    #: legacy reason（A）の有界な証拠の行（`LEGACY_REASON_EVIDENCE_ROW`）。予算に
    #: 収まらなければ件数 + marker。最終 JSON の `unknown_reasons` には使わない
    raw_limitation_evidence: PreparedJson
    plan: SerializationPlan
    options: OutputOptions
    smt_formula: PreparedArtifact = PreparedArtifact(None)
    #: 原因集計（C）のうち trace だけで決まる部分（authority 前に準備する。`None` は未準備）
    cause_evidence: Optional[PreparedJson] = None
    #: 診断（C）の時間のうち trace だけで決まる行（authority 前に準備する。`None` は未準備）
    trace_timings: Optional[PreparedJson] = None

    def __post_init__(self) -> None:
        keys = set()
        for item in self.fields:
            if type(item) is not PreparedField:
                raise TypeError("prepared payload fields must be PreparedField")
            if FIELD_BY_KEY.get(item.key) is None or FIELD_BY_KEY[item.key].owner is not _A:
                raise TypeError(f"{item.key} is not a prepared (A) field")
            if item.key in keys:
                raise ValueError(f"{item.key} prepared twice")
            keys.add(item.key)
        if not is_prepared_json(self.raw_limitation_evidence):
            raise TypeError("raw limitation evidence must be prepared (bounded canonical) JSON")
        for name in ("cause_evidence", "trace_timings"):
            value = getattr(self, name)
            if value is not None and not is_prepared_json(value):
                raise TypeError(f"{name} must be prepared (bounded canonical) JSON")
        if type(self.options) is not OutputOptions:
            raise TypeError("prepared payload needs its OutputOptions")
        if type(self.smt_formula) is not PreparedArtifact:
            raise TypeError("prepared payload needs a PreparedArtifact for the SMT formula")

    def keys(self) -> Tuple[str, ...]:
        return tuple(item.key for item in self.fields if item.json is not None)

    def values_for_output(self) -> Dict[str, Any]:
        """出力へ置く値の **複製**（呼び出し側が壊しても準備済みの値は変わらない）。"""

        return {
            item.key: item.json.value() for item in self.fields if item.json is not None
        }


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

    def prepare(
        self,
        result: Any,
        options: Optional[OutputOptions] = None,
        *,
        strict: bool = True,
        binary_identities: Optional[Tuple[Any, Any]] = None,
    ) -> PreparedSemanticPayload:
        """A を残り予算まで準備して凍結する。意味の field が収まらなければ限界にする。

        意味の field（`LIMITATION`）を先に、診断（`TRUNCATE`）を残りで準備する。
        どちらも `OutputField.prepare` が予算に達した時点で辿るのをやめるので、
        巨大な値を作ってから測ることはない。JSON source でない値は
        `JsonValueRejected`（producer のバグ）。

        `strict=False` は内部エラーを記録した **後** の ERROR 用の準備だけが使う:
        収まらない・JSON にならない field を省いて（`omitted`）、残りを出す。
        """

        if options is None:
            options = OutputOptions.for_result(result)
        context = PreparationContext(
            options, JsonObjectBudget(self.encoding, self.policy.prepared_payload_limit()),
        )
        prepared: List[PreparedField] = []
        prepared_rows = [item for item in RESULT_FIELDS if item.owner is FieldOwner.PREPARED]
        ordered = (
            [item for item in prepared_rows if item.overflow is Overflow.LIMITATION]
            + [item for item in prepared_rows if item.overflow is Overflow.TRUNCATE]
        )
        for item in ordered:
            try:
                row = item.prepare(result, context)
            except JsonBudgetExhausted as exc:
                if not strict:
                    prepared.append(PreparedField(item.key, None, "omitted"))
                    continue
                self._raise_exceeded(context, item.key, exc, prepared)
            except JsonValueRejected:
                if not strict:
                    prepared.append(PreparedField(item.key, None, "omitted"))
                    continue
                raise
            if row is not None:
                prepared.append(row)
        order = _field_order()
        prepared.sort(key=lambda row: order[row.key])
        plan = SerializationPlan(
            encoding=self.encoding,
            max_bytes=self.policy.serialization_bytes,
            headroom_bytes=self.policy.envelope_headroom_bytes,
            prepared_bytes=context.members.total_bytes,
            field_bytes=tuple((row.key, row.encoded_bytes, row.shape) for row in prepared),
        )
        observe_budget_usage(
            BudgetKind.SERIALIZATION_BYTES,
            context.members.total_bytes + self.policy.envelope_headroom_bytes,
            site=PREPARATION_SITE,
        )
        # 判定に使わない準備物（trace の時間・原因集計の trace 部分・legacy の証拠）は 1 つの
        # 予算を共有する: 上限は authority 確定後の field に空けた headroom（これらは C の
        # field の本体か、出力されない内部の証拠）。合計がそれを超えない。出力される C の本体を
        # 先に、出力されない内部の証拠（legacy の証拠）を最後に準備する（内部の証拠が出力の
        # 診断の予算を先に使い切らない）
        diagnostic = JsonBudget(
            None if self.policy.prepared_payload_limit() is None
            else self.policy.envelope_headroom_bytes
        )
        trace_timings = self._prepare_trace_timings(result, diagnostic=diagnostic)
        cause_evidence = self._prepare_cause_evidence(
            result,
            binary_identities if binary_identities is not None else (
                getattr(result, "binary1_content_identity", None),
                getattr(result, "binary2_content_identity", None),
            ),
            diagnostic=diagnostic,
        )
        return PreparedSemanticPayload(
            fields=tuple(prepared),
            raw_limitation_evidence=self._prepare_limitation_evidence(result, diagnostic=diagnostic),
            plan=plan,
            options=options,
            smt_formula=self._prepare_smt_formula(result, options),
            trace_timings=trace_timings,
            cause_evidence=cause_evidence,
        )

    def _prepare_cause_evidence(
        self, result: Any, binary_identities: Tuple[Any, Any], *, diagnostic: JsonBudget,
    ) -> PreparedJson:
        """原因集計の trace 由来の部分を、authority 前に有界に準備する（C、判定に使わない）。

        集計の builder が読む record の表現は、この直列化の作業量（診断用: 超えたら
        限界ではなく marker）へ数えながら作る。authority 確定後の集計は、ここで準備した
        値と canonical reason だけを読む（live な trace を読み直さない）。
        """

        from scripts.function_tracer_pcode.checker.cause_aggregate import (
            build_unknown_cause_aggregate,
        )
        from scripts.function_tracer_pcode.core.budget_policy import serialization_scope

        limit = diagnostic.remaining()
        try:
            with serialization_scope(
                site=CAUSE_EVIDENCE_SITE, target_parts=("cause_evidence",),
                terminal=False, max_bytes=limit, enabled=limit is not None,
            ):
                # 集計と同じ fail-open の入口（失敗は `error` を持つ値になる）
                evidence = build_unknown_cause_aggregate(
                    result, trace_evidence_for=tuple(binary_identities),
                )
            return _charged(diagnostic, self.encoding.prepare(evidence, max_bytes=limit))
        except (JsonBudgetExhausted, JsonValueRejected) as exc:
            return self.encoding.prepare({
                "truncated": True,
                "reason": (
                    BudgetKind.SERIALIZATION_BYTES.value
                    if isinstance(exc, JsonBudgetExhausted) else "not_json"
                ),
            })

    def _prepare_trace_timings(self, result: Any, *, diagnostic: JsonBudget) -> PreparedJson:
        """診断の時間の行（trace 由来）を、authority 前に予算まで準備する（超えたら marker）。"""

        from scripts.function_tracer_pcode.checker.diagnostics import TraceTimingsView

        limit = diagnostic.remaining()
        try:
            return _charged(diagnostic, self.encoding.prepare(TraceTimingsView(result), max_bytes=limit))
        except (JsonBudgetExhausted, JsonValueRejected) as exc:
            return self.encoding.prepare(_truncation_marker(
                "diagnostics.timings.attempts", (),
                remaining_bytes=limit,
                rejected=exc if isinstance(exc, JsonValueRejected) else None,
            ))

    def _prepare_limitation_evidence(self, result: Any, *, diagnostic: JsonBudget) -> PreparedJson:
        """legacy reason の有界な証拠の行を、直列化の予算まで準備する（超えたら marker）。

        行は有界化した legacy reason（G4-b で件数も上限まで）。件数の上限を超えて残さなかった
        reason があれば、最後の行にその件数を置く。
        """

        from scripts.function_tracer_pcode.checker.unknown_reason import LegacyReasonEvidence

        reasons = getattr(result, "unknown_reasons", None) or ()
        overflow = getattr(result, "legacy_reason_overflow", None)
        def rows():
            for record in reasons:
                yield LegacyReasonEvidence(record)
            if overflow:
                yield {"legacy_reason_overflow": int(overflow)}

        try:
            return _charged(diagnostic, self.encoding.prepare(rows(), max_bytes=diagnostic.remaining()))
        except (JsonBudgetExhausted, JsonValueRejected) as exc:
            # 証拠の欠陥で判定を変えない（件数 + marker）
            return self.encoding.prepare({
                "truncated": True,
                "reason": (
                    BudgetKind.SERIALIZATION_BYTES.value
                    if isinstance(exc, JsonBudgetExhausted) else "not_json"
                ),
                "original_items": len(reasons) + int(overflow or 0),
            })

    def _prepare_smt_formula(self, result: Any, options: OutputOptions) -> PreparedArtifact:
        """保存を頼まれた SMT 式を、直列化 1 つ分の予算まで準備する（超えたら省く）。"""

        text = getattr(result, "smt_formula", None)
        if not options.include_smt_formula or not text:
            return PreparedArtifact(None)
        if type(text) is not str:
            raise JsonValueRejected(
                f"{type(text).__qualname__} is not an SMT formula text", path="$.smt_formula",
            )
        limit = self.policy.serialization_bytes
        if limit is not None and _bounded_utf8_length(text, limit) > limit:
            return PreparedArtifact(None, omitted_over_bytes=limit)
        return PreparedArtifact(text)

    def _raise_exceeded(
        self,
        context: PreparationContext,
        key: str,
        exc: JsonBudgetExhausted,
        prepared: List[PreparedField],
    ) -> None:
        members = context.members
        observed = (
            max(members.total_bytes + exc.consumed_bytes, (members.max_bytes or 0) + 1)
            + self.policy.envelope_headroom_bytes
        )
        raise_expression_size_budget_exceeded(
            BudgetKind.SERIALIZATION_BYTES,
            observed=observed,
            limit=self.policy.serialization_bytes,
            site=PREPARATION_SITE,
            target_key=("result_payload", key),
            evidence=(
                f"prepared_bytes_before={members.total_bytes}",
                f"headroom_bytes={self.policy.envelope_headroom_bytes}",
                f"exceeding_field={key}",
                f"fields_before={len(prepared)}",
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


def _charged(budget: JsonBudget, prepared: PreparedJson) -> PreparedJson:
    """準備した値の byte を共有の予算へ足す（上限は準備の `max_bytes` で守られている）。"""

    budget.consumed += prepared.encoded_bytes
    return prepared


def _record_preparation_bug(exc: BaseException) -> None:
    record_internal_bug(InternalError(exc, site=PREPARATION_SITE), site=PREPARATION_SITE)


def finitize_legacy_reasons(result: Any, *, authority_projects_reasons: bool) -> None:
    """G4-b（B5）: legacy reason / recovery action を、件数と重い field の両方で有界にする。

    authority 確定 **前** に 1 回だけ行う。以後 authority の finish（projection の診断・
    legacy の照合）も出力も、置き換えた record しか読まない。reason id・分類は変えない。

    * **件数**: 出力 schema の field の上限と行の下限（`row_min_bytes`）から、その field に
      入り得る行数の上限を導く（`max_rows_within`）。record を 1 件ずつ辿る前に件数だけで比べる。
      - recovery action と、authority が reason を作らない経路（pilot 無し）の reason は、その
        まま出力の行になる: 上限を超えれば判定の前に pair terminal な限界。
      - pilot のある経路の legacy reason は診断にしか使われない: 先頭の canonical reason の
        行数の上限（schema の `max_rows`）までを残し、残りは件数（`legacy_reason_overflow`）
        だけにする。
    * **重い field**: 1 つの作業量（置き換えた record が書かれる出力 field の schema の上限の和）を
      pass 全体で共有して有界にする
      （`checker/unknown_reason.finitize_*`）。使い切った後の証拠は fingerprint の無い要約。
    """

    from scripts.function_tracer_pcode.checker.output_schema import authority_field_bounds
    from scripts.function_tracer_pcode.checker.unknown_reason import (
        UNKNOWN_REASON_ROW,
        UNKNOWN_RECOVERY_ACTION_ROW,
        UnknownReasonRecord,
        UnknownRecoveryAction,
        finitize_unknown_reason_record,
        finitize_unknown_recovery_action,
    )
    from scripts.function_tracer_pcode.core.json_encoding import max_rows_within, row_min_bytes

    bounds = authority_field_bounds(RESULT_JSON_POLICY)
    # 辿ってよい量は、置き換えた record が書かれる出力 field の上限（schema。予算を無効にした
    # policy でも有限）
    work = JsonBudget(bounds["unknown_reasons"].max_bytes + bounds["unknown_recovery_actions"].max_bytes)

    def row_limit(key: str, row: Any) -> int:
        return max_rows_within(bounds[key].max_bytes, row_min_bytes(row, RESULT_JSON_POLICY))

    def over_schema(key: str, count: int, limit: int) -> None:
        raise_expression_size_budget_exceeded(
            BudgetKind.SERIALIZATION_BYTES,
            observed=count,
            limit=limit,
            site=PREPARATION_SITE,
            target_key=("result_payload", key, "rows"),
            evidence=(f"field={key}", f"rows={count}", f"schema_max_rows={limit}"),
        )

    reasons = getattr(result, "unknown_reasons", None)
    if reasons:
        count = len(reasons)
        if authority_projects_reasons:
            # 診断にしか使わない legacy reason: canonical reason の行数の上限（schema）まで残す
            limit = bounds["unknown_reasons"].max_rows
            if count > limit:
                result.legacy_reason_overflow = count - limit
                reasons = reasons[:limit]
        else:
            limit = row_limit("unknown_reasons", UNKNOWN_REASON_ROW)
            if count > limit:
                over_schema("unknown_reasons", count, limit)
        result.unknown_reasons = [
            finitize_unknown_reason_record(item, work=work) if isinstance(item, UnknownReasonRecord) else item
            for item in reasons
        ]
    actions = getattr(result, "unknown_recovery_actions", None)
    if actions:
        limit = row_limit("unknown_recovery_actions", UNKNOWN_RECOVERY_ACTION_ROW)
        if len(actions) > limit:
            over_schema("unknown_recovery_actions", len(actions), limit)
        result.unknown_recovery_actions = [
            finitize_unknown_recovery_action(item, work=work) if isinstance(item, UnknownRecoveryAction) else item
            for item in actions
        ]


def check_prepared_field_bounds(result: Any, *, authority_projects_reasons: bool) -> None:
    """authority 確定 **前** に分かる B の field の大きさを、出力 schema の上限と比べる（G4-b）。

    recovery action の行は authority が作り直さない（finish は reason だけを canonical
    に置き換える）ので、ここで準備して測った byte がそのまま出力の byte になる。authority
    が reason を作らない経路（pilot 無し）では reason の行も同じ。上限を超えるなら、判定の
    前に pair terminal な限界にする（authority 確定後に出力の契約違反で ERROR にしない）。
    canonical reason / relation の大きさは authority の出力で、その上限は authority の
    event stream の契約（#110）。
    """

    from scripts.function_tracer_pcode.checker.output_schema import authority_field_bounds

    bounds = authority_field_bounds(RESULT_JSON_POLICY)
    checked = ["unknown_recovery_actions"]
    if not authority_projects_reasons:
        checked.append("unknown_reasons")
    for key in checked:
        bound = bounds[key]
        try:
            RESULT_JSON_POLICY.measure(FIELD_BY_KEY[key].read(result, None), max_bytes=bound.max_bytes)
        except JsonBudgetExhausted as exc:
            raise_expression_size_budget_exceeded(
                BudgetKind.SERIALIZATION_BYTES,
                observed=exc.consumed_bytes,
                limit=bound.max_bytes,
                site=PREPARATION_SITE,
                target_key=("result_payload", key),
                evidence=(f"field={key}", f"schema_bound={bound.max_bytes}"),
            )


def prepare_pair_output(
    checker: Any,
    result: Any,
    *,
    function_name1: str,
    function_name2: str,
    start_time: float,
    save_formula: bool = False,
) -> Any:
    """G4-b: authority 確定前に出力を準備する。

    出力 option はここで 1 回だけ決める（`OutputOptions.for_result`）。

    * 収まらない（意味の field）: 限界は `raise_limitation` で台帳へ記録されてから
      上がるので、既存の変換（`apply_pair_failure_gate`）で reason 付き UNKNOWN
      （pilot 無しなら `limitation_unattributed` の ERROR）にし、その小さい結果を
      同じ preparer で準備し直す。
    * JSON にならない（producer のバグ）: 内部エラーとして記録し、同じ変換で ERROR
      にする。

    作り直した結果もまた収まらない・JSON にならないのは内部バグ（UNKNOWN / ERROR
    用の結果は解析由来の重い field を持たない）で、記録したうえでその field を
    省いて出す。
    """

    if result is None:
        return result
    from scripts.function_tracer_pcode.checker.pair_execution import (
        apply_pair_failure_gate,
    )

    def _gate(current):
        return apply_pair_failure_gate(
            checker,
            current,
            function_name1=function_name1,
            function_name2=function_name2,
            start_time=start_time,
        )

    policy = active_budget_policy()
    preparer = OutputPreparer(policy)
    options = OutputOptions.for_result(result, save_formula=save_formula)
    identities = tuple(getattr(checker, "_active_binary_content_identities", None) or (None, None))
    authority_projects_reasons = getattr(checker, "v2_dual_write_pilot_connector", None) is not None

    def _finitize_and_check(current):
        finitize_legacy_reasons(current, authority_projects_reasons=authority_projects_reasons)
        check_prepared_field_bounds(current, authority_projects_reasons=authority_projects_reasons)

    try:
        _finitize_and_check(result)
        prepared = preparer.prepare(result, options, binary_identities=identities)
    except (AnalysisLimitation, JsonValueRejected) as exc:
        if isinstance(exc, JsonValueRejected):
            _record_preparation_bug(exc)
        result = _gate(result)
        try:
            _finitize_and_check(result)
            prepared = preparer.prepare(result, options, binary_identities=identities)
        except (AnalysisLimitation, JsonValueRejected) as again:
            _record_preparation_bug(again)
            result = _gate(result)
            try:
                finitize_legacy_reasons(result, authority_projects_reasons=True)
            except AnalysisLimitation as third:  # pragma: no cover - 小さい結果は収まる
                _record_preparation_bug(third)
            prepared = preparer.prepare(
                result, options, strict=False, binary_identities=identities,
            )
    _attach_budget_diagnostics(result, prepared, policy)
    result.prepared_semantic_payload = prepared
    return result


# ---------------------------------------------------------------------------
# B / C と合成
# ---------------------------------------------------------------------------


def _rows(owner: FieldOwner, *, first: Optional[Overflow] = None) -> List[OutputField]:
    rows = [item for item in RESULT_FIELDS if item.owner is owner and item.key != BUNDLE_KEY]
    if first is None:
        return rows
    return [item for item in rows if item.overflow is first] + [
        item for item in rows if item.overflow is not first
    ]


def prepared_payload_for(
    result: Any, *, fallback_policy: Optional[BudgetPolicy] = None,
) -> PreparedSemanticPayload:
    """結果の A（準備済みならそれ、無ければ今準備する）。

    準備済みでないのは pair 境界を通らずに組んだ結果（test の直接構築、起動
    失敗・import 失敗の ERROR）だけ。そのときの上限は `fallback_policy`（production の
    CLI は config の policy を渡す）、無ければ今の pair の policy（scope の外 = 部品単体の
    呼び出しでは無制限）。
    """

    prepared = getattr(result, "prepared_semantic_payload", None)
    if prepared is None:
        policy = fallback_policy if fallback_policy is not None else active_budget_policy()
        return OutputPreparer(policy).prepare(result)
    if type(prepared) is not PreparedSemanticPayload:
        raise TypeError("result.prepared_semantic_payload must be a PreparedSemanticPayload")
    return prepared


def prepared_smt_formula(result: Any) -> PreparedArtifact:
    """`--save-formula` が書く SMT 式（準備済みの成果物だけを返す）。"""

    prepared = getattr(result, "prepared_semantic_payload", None)
    if prepared is None:
        return PreparedArtifact(getattr(result, "smt_formula", None))
    return prepared.smt_formula


def _ordered(parts: Dict[str, Any]) -> Dict[str, Any]:
    order = _field_order()
    return {key: parts[key] for key in sorted(parts, key=lambda key: order[key])}


def result_payload(result: Any, *, fallback_policy: Optional[BudgetPolicy] = None) -> Dict[str, Any]:
    """`EquivalenceResult.to_dict()` の本体 = 最終 envelope の preimage（封印の前）。

    `build_final_result_envelope` と同じ組み立て（同じ上限: A は準備済み、B は schema の上限、
    C は残りの予算）で、上限を超えれば同じ `OutputEnvelopeInvariantViolation`。`to_dict()` と
    人向けの text も有界な値だけを読む。
    """

    return compose_result_preimage(result, fallback_policy=fallback_policy).payload


@dataclass(frozen=True)
class FinalResultEnvelope:
    """CLI が書く最終 payload と、その JSON 文字列（policy 共有の bounded encoder）。"""

    payload: Dict[str, Any]
    text: str
    plan: SerializationPlan
    total_bytes: int
    truncated_metadata: Tuple[str, ...]
    #: 封印（bundle）を足す前の preimage（A + B + C）の byte 数。上限は封印を含む全体に掛かる
    preimage_bytes: int = 0

    def size_line(self) -> str:
        prepared = self.plan.prepared_bytes
        return (
            f"total={self.total_bytes} preimage={self.preimage_bytes} prepared={prepared} "
            f"authority_and_metadata={self.preimage_bytes - prepared} "
            f"bundle={self.total_bytes - self.preimage_bytes} "
            f"headroom={self.plan.headroom_bytes} limit={self.plan.max_bytes} "
            f"truncated_metadata={','.join(self.truncated_metadata) or '-'}"
        )


def _violation(message: str, members: JsonObjectBudget, consumed: int = 0) -> OutputEnvelopeInvariantViolation:
    return OutputEnvelopeInvariantViolation(
        message,
        max_bytes=members.max_bytes or 0,
        requested_bytes=members.total_bytes + consumed,
    )


def _prepare_after_authority(
    item: OutputField,
    result: Any,
    context: PreparationContext,
    prepared: PreparedSemanticPayload,
    *,
    field_max_bytes: Optional[int] = None,
) -> Optional[PreparedField]:
    try:
        return item.prepare(result, context, field_max_bytes=field_max_bytes)
    except JsonBudgetExhausted as exc:
        if field_max_bytes is not None and (
            context.members.remaining_for(item.key) is None
            or field_max_bytes <= context.members.remaining_for(item.key)
        ):
            raise _violation(
                f"{item.key} exceeds its output schema bound of {field_max_bytes} bytes",
                context.members, exc.consumed_bytes,
            ) from exc
        raise _violation(
            f"{item.key} must not be truncated but does not fit the envelope "
            f"(prepared {prepared.plan.prepared_bytes}, headroom {prepared.plan.headroom_bytes})",
            context.members, exc.consumed_bytes,
        ) from exc
    except JsonValueRejected as exc:
        raise _violation(f"{item.key} is not JSON: {exc}", context.members) from exc


@dataclass(frozen=True)
class AuthorityDecisionEnvelope:
    """B: authority が確定した field。authority の attach_* が書いた値だけを読む。

    authority 確定後に同じ `JsonEncodingPolicy.prepare` で canonical にする（切り
    詰めない: 収まらない・JSON にならないのは出力契約の違反）。A の同名 field で
    上書きすることは無い（`RESULT_FIELDS` が所有者を 1 つに決める）。
    """

    fields: Tuple[PreparedField, ...]

    @classmethod
    def prepare(
        cls, result: Any, context: PreparationContext, prepared: PreparedSemanticPayload,
    ) -> "AuthorityDecisionEnvelope":
        from scripts.function_tracer_pcode.checker.output_schema import (
            OutputSchemaMissing,
            authority_field_bounds,
        )

        bounds = authority_field_bounds(context.encoding)
        rows = []
        for item in _rows(FieldOwner.AUTHORITY):
            bound = bounds.get(item.key)
            if bound is None:
                raise OutputSchemaMissing(
                    f"{item.key} has no bound in checker/output_schema.authority_field_bounds"
                )
            row = _prepare_after_authority(
                item, result, context, prepared, field_max_bytes=bound.max_bytes,
            )
            if row is not None:
                rows.append(row)
        return cls(tuple(rows))


@dataclass(frozen=True)
class OutputMetadata:
    """C: 判定に関わらない field（切り詰めてよいものは marker、いけないものは違反）。"""

    fields: Tuple[PreparedField, ...]

    @property
    def truncated(self) -> Tuple[str, ...]:
        return tuple(row.key for row in self.fields if row.shape != "json")

    @classmethod
    def prepare(
        cls, result: Any, context: PreparationContext, prepared: PreparedSemanticPayload,
    ) -> "OutputMetadata":
        rows = []
        for item in _rows(FieldOwner.METADATA, first=Overflow.INVARIANT):
            row = _prepare_after_authority(item, result, context, prepared)
            if row is not None:
                rows.append(row)
        return cls(tuple(rows))


def _compose_members(
    result: Any,
    prepared: PreparedSemanticPayload,
    members: JsonObjectBudget,
    parts: Dict[str, Any],
) -> Tuple[Tuple[str, ...], int]:
    """B と C を `members` の残り予算まで準備して `parts` へ置く。

    切り詰めた C と、切り詰めれば空けられる byte の上限（本体を出した TRUNCATE の C の
    member の byte の和）を返す。
    """

    context = PreparationContext(prepared.options, members)
    authority = AuthorityDecisionEnvelope.prepare(result, context, prepared)
    metadata = OutputMetadata.prepare(result, context, prepared)
    for row in authority.fields + metadata.fields:
        if row.json is not None:
            parts[row.key] = row.json.value()
    freeable = 0
    for row in metadata.fields:
        if row.json is not None and row.shape == "json" and _TRUNCATABLE_METADATA.get(row.key):
            freeable += members.policy.member_bytes(row.key, row.json.encoded_bytes)
    return metadata.truncated, freeable


#: C の field のうち、切り詰めて marker にしてよいもの（schema の `Overflow.TRUNCATE`）
_TRUNCATABLE_METADATA = {
    item.key: item.overflow is Overflow.TRUNCATE
    for item in RESULT_FIELDS if item.owner is FieldOwner.METADATA
}


@dataclass(frozen=True)
class ComposedPreimage:
    """上限の中で組んだ A + B + C（封印の前）。人向けの text と最終 envelope が共有する。"""

    prepared: "PreparedSemanticPayload"
    payload: Dict[str, Any]
    members: JsonObjectBudget
    truncated: Tuple[str, ...]
    #: 切り詰めてよい C を marker にすれば空けられる byte の上限（組み直しで封印が入り得る幅）
    freeable_bytes: int = 0


def compose_result_preimage(
    result: Any, *, fallback_policy: Optional[BudgetPolicy] = None, bundle_reserve: Optional[int] = None,
) -> ComposedPreimage:
    """A + B + C の preimage を上限の中で組む（最終 envelope と `to_dict()` の共通の本体）。

    `bundle_reserve` を渡すと、封印（bundle）の値の byte をその分だけ先に空けてから B / C を
    準備する（切り詰めてよい C が先に marker になる）。
    """

    prepared = prepared_payload_for(result, fallback_policy=fallback_policy)
    plan = prepared.plan
    limit = plan.max_bytes
    members = JsonObjectBudget(plan.encoding, limit)
    parts: Dict[str, Any] = {}
    for item in prepared.fields:
        if item.json is None:
            continue
        members.add(item.key, item.json.encoded_bytes)
        parts[item.key] = item.json.value()
    if limit is not None and members.total_bytes > limit:
        raise _violation(
            "prepared output exceeded the envelope before authority fields "
            f"({members.total_bytes} > {limit} bytes; headroom {plan.headroom_bytes})",
            members,
        )
    if bundle_reserve is not None:
        members.reserve(BUNDLE_KEY, bundle_reserve)
    truncated, freeable = _compose_members(result, prepared, members, parts)
    members.release_reservation()
    return ComposedPreimage(prepared, _ordered(parts), members, tuple(truncated), freeable)


def build_final_result_envelope(
    result: Any,
    *,
    seal: Optional[Callable[[Dict[str, Any]], Mapping[str, Any]]] = None,
    fallback_policy: Optional[BudgetPolicy] = None,
) -> FinalResultEnvelope:
    """A + B + C → 封印 → bounded encode。**Expression / 解析 object を辿らない**。

    **最終 JSON 全体**（A + B + C + finalization bundle）が 1 つの契約の対象で、上限は準備
    したときの plan（authority 確定前に決めた値 = `serialization_bytes`）。

    * A は準備済みの値をそのまま置き、B は出力 schema の field ごとの上限まで（切り詰め
      ない）、C は残り予算まで（切り詰めてよいものだけ marker）準備する。
    * 封印（bundle）は preimage（A + B + C）全体の digest を持つ receipt で、**残りの予算を
      上限にして** 準備する（切り詰めない）。収まらなければ出力の契約違反。
    * 書き出しは契約の上限で行い（作った大きさを上限にしない）、書いた byte と勘定の
      一致を別に確かめる。
    * 違反は `OutputEnvelopeInvariantViolation`（確定済みの判定は変えない。呼ぶ側が内部
      エラーの ERROR として durable にする）。

    封印を **組み立てる** 作業（authority の event stream の codec・replay）の大きさは
    authority の event stream に比例し、その上限の契約は #110 に依存する（本 function が
    有界にするのは、組み立てた封印を出力へ写す作業と最終 JSON の大きさ）。
    """

    return finalize_result_envelope(
        compose_result_preimage(result, fallback_policy=fallback_policy), seal=seal,
        recompose=lambda reserve: compose_result_preimage(
            result, fallback_policy=fallback_policy, bundle_reserve=reserve,
        ),
    )


def finalize_result_envelope(
    composed: ComposedPreimage,
    *,
    seal: Optional[Callable[[Dict[str, Any]], Mapping[str, Any]]] = None,
    recompose: Optional[Callable[[int], ComposedPreimage]] = None,
) -> FinalResultEnvelope:
    """組んだ preimage に封印を足し、契約の上限で書く（`build_final_result_envelope` の後半）。

    封印が残りに収まらず、preimage に切り詰めてよい診断（C）があれば、封印の大きさ（契約の
    上限の中で数えた値）を先に空けて組み直し（`recompose`）、封印し直す。封印は preimage の
    digest を持つので、preimage が変われば作り直す（大きさは preimage の中身に依らない）。
    それでも収まらなければ出力の契約違反。
    """

    prepared, preimage, members, truncated = (
        composed.prepared, composed.payload, composed.members, composed.truncated,
    )
    plan = prepared.plan
    encoding = plan.encoding
    limit = plan.max_bytes
    preimage_bytes = members.total_bytes
    payload = preimage
    total = preimage_bytes
    if seal is not None:
        room = members.remaining_for(BUNDLE_KEY)
        try:
            bundle = encoding.prepare(seal(preimage), max_bytes=room)
        except JsonBudgetExhausted as exc:
            bundle = None
            if recompose is not None and composed.freeable_bytes > 0:
                # 切り詰めてよい診断が場所を取っている。封印の大きさを、組み直しで空き得る幅
                # （残り + 切り詰められる byte）の中で数え（封印は作り直す: 生成器を読み直さない）、
                # その分を先に空けて組み直し、新しい preimage を封印し直す
                try:
                    needed = encoding.prepare(
                        seal(preimage), max_bytes=room + composed.freeable_bytes,
                    ).encoded_bytes
                except (JsonBudgetExhausted, JsonValueRejected):
                    needed = None
                if needed is not None:
                    composed = recompose(needed)
                    prepared, preimage, members, truncated = (
                        composed.prepared, composed.payload, composed.members, composed.truncated,
                    )
                    preimage_bytes = members.total_bytes
                    room = members.remaining_for(BUNDLE_KEY)
                    try:
                        bundle = encoding.prepare(seal(preimage), max_bytes=room)
                    except JsonBudgetExhausted:
                        bundle = None
            if bundle is None:
                raise _violation(
                    f"{BUNDLE_KEY} does not fit the rest of the envelope "
                    f"(> {room} bytes after a {preimage_bytes}-byte preimage)",
                    members,
                ) from exc
        except JsonValueRejected as exc:
            raise _violation(f"{BUNDLE_KEY} is not JSON: {exc}", members) from exc
        payload = dict(preimage)
        payload[BUNDLE_KEY] = bundle.value()
        payload = _ordered(payload)
        members.add(BUNDLE_KEY, bundle.encoded_bytes)
        total = members.total_bytes
    try:
        # 契約の上限で書く（勘定が正しければ `total` 以下で、上限を超える前に止まる）
        text_value = encoding.encode_bounded(payload, max_bytes=limit)
    except JsonOutputLimitExceeded as exc:  # pragma: no cover - 勘定と書き出しの不一致
        raise OutputEnvelopeInvariantViolation(
            "the encoded envelope exceeds the output contract "
            f"(needed {exc.requested_bytes} > {exc.max_bytes} bytes)",
            max_bytes=exc.max_bytes,
            requested_bytes=exc.requested_bytes,
        ) from exc
    from scripts.function_tracer_pcode.core.render_output import utf8_length

    written = utf8_length(text_value)
    if written != total:  # pragma: no cover - 勘定と書き出しの不一致（内部バグ）
        raise OutputEnvelopeInvariantViolation(
            f"the encoded envelope ({written} bytes) differs from its accounted size ({total} bytes)",
            max_bytes=limit,
            requested_bytes=written,
        )
    return FinalResultEnvelope(
        payload=payload,
        text=text_value,
        plan=plan,
        total_bytes=total,
        truncated_metadata=truncated,
        preimage_bytes=preimage_bytes,
    )


__all__ = [
    "ABSENT",
    "AuthorityDecisionEnvelope",
    "OutputMetadata",
    "BUNDLE_KEY",
    "FIELD_BY_KEY",
    "FieldOwner",
    "FinalResultEnvelope",
    "OutputEnvelopeInvariantViolation",
    "OutputField",
    "OutputOptions",
    "OutputPreparer",
    "Overflow",
    "PREPARED_SOURCE_ATTRIBUTES",
    "PreparationContext",
    "PreparedArtifact",
    "PreparedField",
    "PreparedPayloadStale",
    "PreparedSemanticPayload",
    "RESULT_FIELDS",
    "SerializationPlan",
    "ComposedPreimage",
    "build_final_result_envelope",
    "compose_result_preimage",
    "finalize_result_envelope",
    "check_prepared_field_bounds",
    "fields_owned_by",
    "finitize_legacy_reasons",
    "prepare_pair_output",
    "prepared_payload_for",
    "prepared_smt_formula",
    "result_payload",
]
