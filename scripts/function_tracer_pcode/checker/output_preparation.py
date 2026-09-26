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

import types
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
from scripts.function_tracer_pcode.core import json_encoding, live_values
from scripts.function_tracer_pcode.core import read_limits
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
    builtin_str,
    bounded_repr,
    exception_text,
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

    @staticmethod
    def for_result(result: Any, *, save_formula: bool = False) -> "OutputOptions":
        """結果の flag（workflow が `checker.debug` から決めた値）を **ここで 1 回だけ** 読む。"""

        return OutputOptions(
            include_debug_trace=live_values.as_bool(live_values.attribute(result, "emit_debug_trace", True)),
            include_smt_formula=live_values.as_bool(save_formula),
        )

    def plain(self) -> "OutputOptions":
        """同じ選択の複製（field を plain な `bool` として読み直す。準備済みの payload から読むとき）。"""

        return OutputOptions(
            include_debug_trace=live_values.as_bool(self.include_debug_trace),
            include_smt_formula=live_values.as_bool(self.include_smt_formula),
        )


class _Absent:
    __slots__ = ()

    def __repr__(self) -> str:  # pragma: no cover - debug 表示
        return "ABSENT"


#: `read` が「この field を出さない」ときに返す値。
ABSENT = _Absent()

#: `read(result, options)` → JSON source か `ABSENT`。
class ReadKind(Enum):
    """結果の field の読み方の種類（閉じた集合。任意の callable は受けない）。"""

    ATTRIBUTE = "attribute"      # 属性の値
    PRESENT = "present"          # 属性の値（`None` なら出さない）
    TRUTHY = "truthy"            # 属性の値（偽なら出さない）
    OR_NONE = "or_none"          # 属性の値（偽なら `None`）
    EACH = "each"                # 属性の列を 1 要素ずつ（`each`）
    MESSAGE = "message"          # 失敗の自由文（出力 schema の文字数まで）
    METHOD = "method"            # package の結果の型の method（引数なし）
    FUNCTION = "function"        # この module の読み方の関数（`_read_by_function` の登録）


@dataclass(frozen=True)
class Read:
    """field の読み方: `kind` と、読む結果の属性（method・関数）の名前。"""

    kind: ReadKind
    name: str


def _attribute(name: str) -> Read:
    return Read(ReadKind.ATTRIBUTE, name)


def _method(name: str) -> Read:
    return Read(ReadKind.METHOD, name)


def _function(name: str) -> Read:
    return Read(ReadKind.FUNCTION, name)


def _each(name: str) -> Read:
    return Read(ReadKind.EACH, name)


def _or_none(name: str) -> Read:
    return Read(ReadKind.OR_NONE, name)


@dataclass(frozen=True)
class PreparedField:
    """準備した 1 field。値は `PreparedJson`（canonical・byte 数つき）だけ。"""

    key: str
    json: Optional[PreparedJson]
    #: `json` / `truncation_marker` / `omitted`
    shape: str

    def __post_init__(self) -> None:
        shape = self.shape
        if type(shape) is not str:
            raise ValueError(f"unknown prepared field shape {bounded_repr(shape)}")
        if shape not in ("json", "truncation_marker", "omitted"):
            raise ValueError(f"unknown prepared field shape {shape!r}")
        if (self.json is None) != (shape == "omitted"):
            raise TypeError(f"{builtin_str(self.key)}: only an omitted field lacks its prepared JSON")
        if self.json is not None and not is_prepared_json(self.json):
            raise TypeError(
                f"{builtin_str(self.key)}: a prepared field holds only JsonEncodingPolicy.prepare output"
            )

    @property
    def encoded_bytes(self) -> int:
        prepared = self.json
        if type(prepared) is PreparedJson:
            return live_values.as_int(prepared.encoded_bytes)
        return 0

    def field_key(self) -> str:
        return live_values.as_str(self.key)

    def field_shape(self) -> str:
        return live_values.as_str(self.shape)

    def has_json(self) -> bool:
        return self.json is not None

    def json_value(self) -> Any:
        """準備した値の複製（`PreparedJson.value`）。"""

        prepared = self.json
        if type(prepared) is not PreparedJson:
            raise TypeError(f"{builtin_str(self.key)}: the field has no prepared JSON")
        return prepared.value()


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

    # 組み込みの振る舞いの容器だけ長さを読む（上書きした `__len__` を呼ばない）
    count = (
        live_values.size(source)
        if live_values.builtin_sequence(source) or live_values.builtin_mapping(source) is not None
        else None
    )
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


def _prepare_json(encoding: Any, source: Any, *, max_bytes: Optional[int]) -> PreparedJson:
    """`encoding`（`JsonEncodingPolicy` そのもの）の walker で `source` を `max_bytes` まで準備する。"""

    if type(encoding) is not JsonEncodingPolicy:
        raise TypeError("output preparation needs an exact JsonEncodingPolicy")
    return encoding.prepare(source, max_bytes=max_bytes)


class _ReadFailed:
    """読み方が落ちた field の値（`JsonValueRejected` を持つ）。"""

    __slots__ = ("rejected",)

    def __init__(self, rejected: JsonValueRejected) -> None:
        self.rejected = rejected


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
        if type(source) is _ReadFailed:
            raise source.rejected
        if remaining is not None and remaining < 0:
            raise JsonBudgetExhausted(consumed_bytes=0, max_bytes=remaining)
        prepared = _prepare_json(encoding, source, max_bytes=remaining)
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

        return self.prepare_source(
            self.read_source(result, context.options), context, field_max_bytes=field_max_bytes,
        )

    def read_source(self, result: Any, options: "OutputOptions") -> Any:
        """`read` の値。切り詰めてよい診断の読み方が値の不備で落ちたら、その値は JSON に
        ならない（`_prepare_member` が marker にする。診断の欠陥で判定を変えない）。
        """

        from scripts.function_tracer_pcode.core.json_encoding import PRODUCER_FAILURES

        try:
            return _read(self.read, result, options)
        except PRODUCER_FAILURES as exc:
            if self.overflow is not Overflow.TRUNCATE:
                # 切り詰めてはいけない field の読み方の失敗は、その owner の契約の失敗のまま上げる
                # （A は準備の内部エラー、B / C は出力の失敗の ERROR）
                raise
            return _ReadFailed(JsonValueRejected(
                f"reader failed ({exception_text(exc)})", path=f"$.{self.key}",
            ))

    def prepare_source(
        self,
        source: Any,
        context: PreparationContext,
        *,
        field_max_bytes: Optional[int] = None,
    ) -> Optional[PreparedField]:
        """読んだ source（`read` の値）を準備する（`ABSENT` なら出さない）。"""

        if source is ABSENT:
            return None
        return _prepare_member(
            context, self.key, source, self.overflow, field_max_bytes=field_max_bytes,
        )


# ---------------------------------------------------------------------------
# field の読み方（JSON source を返すだけ。表現は作らない）
# ---------------------------------------------------------------------------


def _when_truthy(attribute: str) -> Read:
    return Read(ReadKind.TRUTHY, attribute)


def _when_present(attribute: str) -> Read:
    return Read(ReadKind.PRESENT, attribute)


def _message(attribute: str) -> Read:
    """失敗の自由文（出力 schema の文字数まで。超えた分は明示の marker）。"""

    return Read(ReadKind.MESSAGE, attribute)


def _read(spec: Read, result: Any, options: OutputOptions) -> Any:
    """読み方 1 つを実行する（結果の live な値は owner の API だけで読む）。"""

    kind = spec.kind
    if kind is ReadKind.METHOD:
        return _result_method(result, spec.name)
    if kind is ReadKind.FUNCTION:
        return _read_by_function(spec.name, result, options)
    value = live_values.attribute(result, spec.name)
    if kind is ReadKind.ATTRIBUTE:
        return value
    if kind is ReadKind.PRESENT:
        return ABSENT if value is None else value
    if kind is ReadKind.TRUTHY:
        return value if value is not None and live_values.as_bool(value) else ABSENT
    if kind is ReadKind.OR_NONE:
        return value if value is not None and live_values.as_bool(value) else None
    if kind is ReadKind.EACH:
        return each(value)
    if kind is ReadKind.MESSAGE:
        from scripts.function_tracer_pcode.checker.output_schema import MESSAGE_MAX_CHARS

        return text(value, MESSAGE_MAX_CHARS)
    raise TypeError("unknown read kind")  # pragma: no cover - 閉じた集合の追加漏れ


def _result_method(result: Any, name: str) -> Any:
    """結果の型（`EquivalenceResult`）の引数なしの method（閉じた名前の集合。型を確かめて名前で呼ぶ）。"""

    from scripts.function_tracer_pcode.checker.result import EquivalenceResult

    if type(result) is not EquivalenceResult:
        raise TypeError(f"{live_values.type_name(type(result))} is not an EquivalenceResult")
    if name == "is_timeout":
        return result.is_timeout()
    if name == "get_effective_function1_signature":
        return result.get_effective_function1_signature()
    if name == "get_effective_function2_signature":
        return result.get_effective_function2_signature()
    raise TypeError(f"no registered result method {name}")


def _read_by_function(name: str, result: Any, options: OutputOptions) -> Any:
    """登録した読み方の関数（名前で呼ぶ。関数の値を field に持たない）。"""

    if name == "mips64_abi_constraints":
        return _mips64_abi_constraints(result, options)
    if name == "debug_trace":
        return _debug_trace(result, options)
    if name == "decision_receipt":
        return _decision_receipt(result, options)
    if name == "conditional_decision_receipt":
        return _conditional_decision_receipt(result, options)
    if name == "unknown_recovery_backlog":
        return _unknown_recovery_backlog(result, options)
    if name == "diagnostics":
        return _diagnostics(result, options)
    if name == "unknown_cause_aggregate":
        return _unknown_cause_aggregate(result, options)
    raise TypeError(f"no registered reader function {name}")


def _mips64_abi_constraints(r: Any, _o: OutputOptions) -> Any:
    constraints = live_values.attribute(r, "mips64_abi_constraints")
    if constraints is None or not live_values.as_bool(constraints):
        return ABSENT
    return pairs_of(_abi_constraint_pairs(constraints))


def _abi_constraint_pairs(constraints: Any) -> Any:
    """ABI 制約の (key, {signedness, narrow_bits})（1 組ずつ。mapping を先に写さない）。"""

    for key, value in live_values.items_of(constraints):
        # 値は (signedness, narrow_bits) の 2 つ組（旧 unpack と同じく 2 つでなければ `ValueError`）。
        # 列全体を先に写さない（大きさを確かめてから 2 つだけ読む）
        if live_values.size(value) != 2:
            raise ValueError("an ABI constraint is a (signedness, narrow_bits) pair")
        members = live_values.elements_of(value)
        signedness = next(members)
        narrow_bits = next(members)
        yield key, inline(("signedness", signedness), ("narrow_bits", narrow_bits))


def _debug_trace(r: Any, o: OutputOptions) -> Any:
    # Issue #128 PR-128-B: trace は常に object 上に在り、debug 指定のときだけ JSON へ
    # 添付する（指定は `OutputOptions` が準備時に 1 回決める）。
    trace = live_values.attribute(r, "debug_trace")
    if trace is not None and live_values.as_bool(trace) and o.include_debug_trace:
        return trace
    return ABSENT


def _decision_receipt(r: Any, _o: OutputOptions) -> Any:
    from scripts.function_tracer_pcode.authority.decision.decision import DecisionReceipt

    receipt = live_values.attribute(r, "decision_receipt")
    if receipt is not None:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import decision_receipt_payload
        from scripts.function_tracer_pcode.checker.result import decided_outcome_of

        if type(receipt) is not DecisionReceipt:
            raise TypeError("the decision receipt column requires an exact DecisionReceipt")
        decided_outcome_of(r)
        return decision_receipt_payload(receipt)
    if live_values.as_bool(live_values.attribute(r, "canonical_decision_required", False)):
        raise ValueError("canonical serialization lacks DecisionReceipt")
    return None


def _conditional_decision_receipt(r: Any, _o: OutputOptions) -> Any:
    from scripts.function_tracer_pcode.authority.decision.conditional import ConditionalDecisionReceipt

    receipt = live_values.attribute(r, "conditional_decision_receipt")
    if receipt is not None:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            conditional_decision_receipt_payload,
        )

        if type(receipt) is not ConditionalDecisionReceipt:
            raise TypeError("the conditional column requires an exact ConditionalDecisionReceipt")
        return conditional_decision_receipt_payload(receipt)
    if live_values.attribute(r, "conditional_outcome") is not None:
        raise ValueError("conditional outcome without its ConditionalDecisionReceipt")
    return None


def _unknown_recovery_backlog(r: Any, _o: OutputOptions) -> Any:
    from scripts.function_tracer_pcode.checker.unknown_reason import recovery_backlog_source

    return recovery_backlog_source(live_values.attribute(r, "unknown_reasons"))


def _diagnostics(r: Any, _o: OutputOptions) -> Any:
    from scripts.function_tracer_pcode.checker.diagnostics import result_diagnostics_payload

    return result_diagnostics_payload(r, lazy=True)


def _unknown_cause_aggregate(r: Any, _o: OutputOptions) -> Any:
    # Issue #128: 原因分析の compact 集計は常時出す。CLI が封印の前に確定させる
    # （`attach_cause_aggregate`）。確定していなければその場で作る。どちらも trace 由来の
    # 部分は authority 前に準備した値（`PreparedSemanticPayload.cause_evidence`）を読み、
    # authority 後に live な trace を辿らない（残りは canonical reason だけ）。
    aggregate = live_values.attribute(r, "unknown_cause_aggregate")
    if aggregate is not None:
        return aggregate
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
    OutputField("is_equivalent", _B, _attribute("is_equivalent"), _INV),
    OutputField("function1_name", _A, _attribute("function1_name"), _LIMIT),
    OutputField("function2_name", _A, _attribute("function2_name"), _LIMIT),
    OutputField("binary1_name", _A, _attribute("binary1_name"), _LIMIT),
    OutputField("binary2_name", _A, _attribute("binary2_name"), _LIMIT),
    # content identity は `check_from_binaries` が boundary の **後** に書く
    OutputField("binary1_content_identity", _C, _attribute("binary1_content_identity"), _INV),
    OutputField("binary2_content_identity", _C, _attribute("binary2_content_identity"), _INV),
    OutputField("function1_identity", _A, _attribute("function1_identity"), _LIMIT),
    OutputField("function2_identity", _A, _attribute("function2_identity"), _LIMIT),
    OutputField("function1_signature", _A, _attribute("function1_signature"), _LIMIT),
    OutputField("function2_signature", _A, _attribute("function2_signature"), _LIMIT),
    OutputField(
        "effective_function1_signature", _A,
        _method("get_effective_function1_signature"), _LIMIT,
    ),
    OutputField(
        "effective_function2_signature", _A,
        _method("get_effective_function2_signature"), _LIMIT,
    ),
    OutputField(
        "function1_signature_hypotheses", _A,
        _attribute("function1_signature_hypotheses"), _LIMIT,
    ),
    OutputField(
        "function2_signature_hypotheses", _A,
        _attribute("function2_signature_hypotheses"), _LIMIT,
    ),
    OutputField("solver_results", _A, _or_none("solver_results"), _LIMIT),
    OutputField("counterexample", _A, _attribute("counterexample"), _LIMIT),
    OutputField("total_time", _C, _attribute("total_time"), _INV),
    OutputField("error_message", _B, _message("error_message"), _INV),
    OutputField("failure_status", _B, _attribute("failure_status"), _INV),
    OutputField("failure_message", _B, _message("failure_message"), _INV),
    OutputField("type_fix_result", _A, _attribute("type_fix_result"), _LIMIT),
    OutputField("retry_count", _A, _attribute("retry_count"), _LIMIT),
    OutputField("is_timeout", _B, _method("is_timeout"), _INV),
    OutputField("final_outcome", _B, _attribute("final_outcome"), _INV),
    OutputField("decision_receipt", _B, _function("decision_receipt"), _INV),
    OutputField("conditional_outcome", _B, _attribute("conditional_outcome"), _INV),
    OutputField("conditional_decision_receipt", _B, _function("conditional_decision_receipt"), _INV),
    OutputField("c_active_base", _B, _attribute("canonical_c_active_base"), _INV),
    OutputField("q_open_base", _B, _attribute("canonical_q_open_base"), _INV),
    OutputField("constrained_fragments", _A, _attribute("constrained_fragments"), _LIMIT),
    # solver / pair の件数。判定には効かない観測（reporting は読むが、欠けても
    # 判定の再構成には要らない）
    OutputField("pairwise_stats", _C, _attribute("pairwise_stats"), _TRUNC),
    OutputField("pairwise_debug_stats", _C, _attribute("pairwise_debug_stats"), _TRUNC),
    OutputField("unknown_reasons", _B, _each("unknown_reasons"), _INV),
    OutputField(
        "unknown_recovery_actions", _B,
        _each("unknown_recovery_actions"), _INV,
    ),
    OutputField("unknown_recovery_backlog", _B, _function("unknown_recovery_backlog"), _INV),
    OutputField(
        "decision_gated_by_pending_proof", _B,
        _attribute("decision_gated_by_pending_proof"), _INV,
    ),
    OutputField("sat_pair_info", _A, _attribute("sat_pair_info"), _LIMIT),
    # 通った phase / stage の足跡（診断）
    OutputField("stage_path", _C, _attribute("stage_path"), _TRUNC),
    OutputField("diagnostics", _C, _function("diagnostics"), _TRUNC),
    OutputField("unknown_cause_aggregate", _C, _function("unknown_cause_aggregate"), _TRUNC),
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
    OutputField("mips64_abi_constraints", _A, _function("mips64_abi_constraints"), _LIMIT),
    # 判定に関わらないので、予算を超えるなら件数 + marker に置き換える。
    OutputField("debug_trace", _A, _function("debug_trace"), _TRUNC),
)

FIELD_BY_KEY: Dict[str, OutputField] = {item.key: item for item in RESULT_FIELDS}


def _field_order() -> Dict[str, int]:
    """今の `RESULT_FIELDS` の並び（出力の key 順）。"""

    return {item.key: index for index, item in enumerate(RESULT_FIELDS)}

#: A の field が読む結果の属性。準備の後にこれらを **差し替える** のは内部バグ
#: （準備済みの値が結果を表さなくなる）で、`EquivalenceResult.__setattr__` が拒む。
#: 読み方と一致していることは architecture test が AST で確かめる。
PREPARED_SOURCE_ATTRIBUTES = frozenset(
    # A の読み方は field と同名の結果の属性を読む（`test_prepared_readers_read_only_the_declared_
    # source_attributes` が読み方の AST と照らす）。A の行を足せばここは自動で追従する
    [item.key for item in RESULT_FIELDS if item.owner is FieldOwner.PREPARED]
    # 成果物として準備する SMT 式（field ではない）
    + ["smt_formula"]
)


def fields_owned_by(owner: FieldOwner) -> Tuple[str, ...]:
    return tuple(item.key for item in RESULT_FIELDS if item.owner is owner)


class PreparedPayloadStale(AnalysisFailureError):
    """準備した後で A の元になる属性を差し替えようとした（内部バグ）。"""


class OutputEnvelopeInvariantViolation(AnalysisFailureError):
    """authority 確定後の field が予約した headroom に収まらない / JSON にならない。

    **意味の限界ではない**。判定は確定済みなので UNKNOWN へ変えず、出力の契約
    違反（内部エラー）として扱う（`FINAL_ENVELOPE_SITE`）。
    """

    def __init__(self, message: str, *, max_bytes: Optional[int], requested_bytes: Optional[int]) -> None:
        super().__init__(message)
        # 大きさの違反でない（準備・封印の内部の不備）なら `None`
        self.max_bytes = _optional_int(max_bytes)
        self.requested_bytes = _optional_int(requested_bytes)


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

    # 準備済みの payload から読む値（plain な値として読み直す）

    def limit(self) -> Optional[int]:
        return _optional_int(self.max_bytes)

    def headroom(self) -> int:
        return live_values.as_int(self.headroom_bytes)

    def prepared_size(self) -> int:
        return live_values.as_int(self.prepared_bytes)

    def encoder(self) -> JsonEncodingPolicy:
        encoding = self.encoding
        if type(encoding) is not JsonEncodingPolicy:
            raise TypeError("a serialization plan needs an exact JsonEncodingPolicy")
        return encoding

    def to_diagnostic(self) -> Dict[str, Any]:
        largest = sorted(self.field_bytes, key=_largest_first)[:5]
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


def _largest_first(row: Tuple[str, int, str]) -> Tuple[int, str]:
    """field の大きさの行の整列の key（大きい順、同じなら key の順）。"""

    return (-row[1], row[0])


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
        for item in live_values.elements_of(self.fields):
            if type(item) is not PreparedField:
                raise TypeError("prepared payload fields must be PreparedField")
            key = item.field_key()
            if FIELD_BY_KEY.get(key) is None or FIELD_BY_KEY[key].owner is not _A:
                raise TypeError(f"{key} is not a prepared (A) field")
            if key in keys:
                raise ValueError(f"{key} prepared twice")
            keys.add(key)
        if not is_prepared_json(self.raw_limitation_evidence):
            raise TypeError("raw limitation evidence must be prepared (bounded canonical) JSON")
        for name in ("cause_evidence", "trace_timings"):
            value = live_values.attribute(self, name)
            if value is not None and not is_prepared_json(value):
                raise TypeError(f"{name} must be prepared (bounded canonical) JSON")
        if type(self.options) is not OutputOptions:
            raise TypeError("prepared payload needs its OutputOptions")
        if type(self.smt_formula) is not PreparedArtifact:
            raise TypeError("prepared payload needs a PreparedArtifact for the SMT formula")

    def payload_plan(self) -> SerializationPlan:
        plan = self.plan
        if type(plan) is not SerializationPlan:
            raise TypeError("prepared payload needs its SerializationPlan")
        return plan

    def output_options(self) -> OutputOptions:
        options = self.options
        if type(options) is not OutputOptions:
            raise TypeError("prepared payload needs its OutputOptions")
        return options.plain()

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


def output_contract_policy(policy: BudgetPolicy) -> BudgetPolicy:
    """出力の準備が使う policy: 直列化の byte の予算は authority の契約の上限（結果の preimage）まで。

    調査用に予算を外した（`off`）policy・契約より大きい予算でも、準備の作業量は封印が受け取れる
    preimage の上限を超えない（作業量を受け取らない準備を作らない）。上限の内側の予算はそのまま。
    上限で置き換えるときは headroom も有効な値にする: schema が要る headroom 以上、上限の半分以下
    （payload の余地を残す。設定の組み合わせで policy を作れない値にしない）。準備した payload と
    判定に使わない準備物（headroom を共有する）の和は上限を超えない。
    """

    from dataclasses import replace

    from scripts.function_tracer_pcode.authority.event_contract import AUTHORITY_EVENT_CONTRACT
    from scripts.function_tracer_pcode.checker.output_schema import required_headroom_bytes

    ceiling = AUTHORITY_EVENT_CONTRACT.max_result_preimage_units
    configured = policy.serialization_bytes
    if configured is not None and configured <= ceiling:
        return policy
    headroom = min(max(policy.envelope_headroom_bytes, required_headroom_bytes()), ceiling // 2)
    return replace(policy, serialization_bytes=ceiling, envelope_headroom_bytes=headroom)


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
        self.policy = output_contract_policy(policy)
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
                # `RESULT_FIELDS` の行（package の定数）の準備
                row = OutputField.prepare(item, result, context)
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
        prepared = _in_field_order(prepared)
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
        diagnostic = JsonBudget(self.policy.envelope_headroom_bytes)
        trace_timings = self._prepare_trace_timings(result, diagnostic=diagnostic)
        cause_evidence = self._prepare_cause_evidence(
            result,
            binary_identities if binary_identities is not None else (
                live_values.attribute(result, "binary1_content_identity"),
                live_values.attribute(result, "binary2_content_identity"),
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
            ) as work:
                # 集計と同じ fail-open の入口（失敗は `error` を持つ値になる）
                evidence = build_unknown_cause_aggregate(
                    result, trace_evidence_for=tuple(binary_identities),
                )
            # 集計を組んだ作業量も診断の共有の予算へ 1 回だけ数える（組む仕事と書く byte は別の単位）
            if limit is not None:
                diagnostic.charge(work.consumed)
            return _charged(
                diagnostic, _prepare_json(self.encoding, evidence, max_bytes=diagnostic.remaining()),
            )
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
            return _charged(diagnostic, _prepare_json(self.encoding, TraceTimingsView(result), max_bytes=limit))
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

        reasons = live_values.attribute(result, "unknown_reasons")
        if not _truthy(reasons):
            reasons = ()
        overflow = live_values.attribute(result, "legacy_reason_overflow")
        overflow_count = live_values.as_int(overflow) if _truthy(overflow) else 0
        try:
            return _charged(diagnostic, _prepare_json(
                self.encoding, _limitation_rows(reasons, overflow_count), max_bytes=diagnostic.remaining(),
            ))
        except (JsonBudgetExhausted, JsonValueRejected) as exc:
            # 証拠の欠陥で判定を変えない（件数 + marker）
            return self.encoding.prepare({
                "truncated": True,
                "reason": (
                    BudgetKind.SERIALIZATION_BYTES.value
                    if isinstance(exc, JsonBudgetExhausted) else "not_json"
                ),
                "original_items": live_values.size(reasons) + overflow_count,
            })

    def _prepare_smt_formula(self, result: Any, options: OutputOptions) -> PreparedArtifact:
        """保存を頼まれた SMT 式を、直列化 1 つ分の予算まで準備する（超えたら省く）。"""

        if not live_values.as_bool(live_values.attribute(options, "include_smt_formula")):
            return PreparedArtifact(None)
        text = live_values.attribute(result, "smt_formula")
        if text is None:
            return PreparedArtifact(None)
        if type(text) is not str:
            if not live_values.as_bool(text):
                return PreparedArtifact(None)
            raise JsonValueRejected(
                f"{live_values.type_name(type(text))} is not an SMT formula text", path="$.smt_formula",
            )
        if not text:
            return PreparedArtifact(None)
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


def _truthy(value: Any) -> bool:
    """`bool(value)`（`None` は偽。scalar・組み込みの振る舞いの容器・package の record だけを読む）。"""

    return value is not None and live_values.as_bool(value)


def _optional_int(value: Any) -> Optional[int]:
    """`None` か plain な `int`（package の record の field を読み直す）。"""

    return None if value is None else live_values.as_int(value)


def _plain_key(key: Any) -> Any:
    """mapping の key の plain な値（scalar だけ。それ以外は `TypeError`）。"""

    plain = live_values.plain_scalar(key)
    if plain is live_values.NOT_PLAIN:
        raise TypeError(f"{live_values.type_name(type(key))} is not a plain mapping key")
    return plain


def _in_field_order(rows: List[Any]) -> List[Any]:
    """準備した field を出力の並び（`RESULT_FIELDS` の順）に並べる（安定。key は field 名の位置）。"""

    order = _field_order()
    positions = []
    for index, row in enumerate(rows):
        if type(row) is not PreparedField:
            raise TypeError("prepared rows are PreparedField only")
        positions.append((order[row.field_key()], index))
    positions.sort()
    return [rows[index] for _position, index in positions]


def _limitation_rows(reasons: Any, overflow: int):
    """legacy reason の有界な証拠の行（walker が 1 行ずつ引き出す）と、残さなかった件数の行。"""

    from scripts.function_tracer_pcode.checker.unknown_reason import LegacyReasonEvidence

    for record in live_values.elements_of(reasons):
        yield LegacyReasonEvidence(record)
    if overflow:
        yield {"legacy_reason_overflow": overflow}


def _attach_budget_diagnostics(result: Any, prepared: PreparedSemanticPayload, policy) -> None:
    """予算の値・観測値・準備の内訳を診断へ書く（C、判定に使わない）。"""

    current = live_values.attribute(result, "diagnostics")
    diagnostics: Dict[Any, Any] = {}
    if _truthy(current):
        # 組み込みの振る舞いの mapping の複製（key は scalar だけ）。作業量を受け取らない複製は
        # live_values の固定の上限の組まで（先頭から）で、外は件数の marker（診断だけ。判定・canonical
        # reason は読まないので outcome は変わらない）
        for key, value in read_limits.prefix_within_limit(live_values.items_of(current)):
            diagnostics[_plain_key(key)] = value
        omitted = read_limits.omitted_beyond_limit(current)
        if omitted:
            diagnostics["diagnostics_overflow"] = {
                "truncated": True, "keys": live_values.size(current), "kept": live_values.SCAN_LIMIT,
            }
    diagnostics["expression_budget"] = {
        "policy": policy.to_diagnostic(),
        "observed": budget_observations(),
        "serialization": prepared.plan.to_diagnostic(),
    }
    live_values.set_state(result, "diagnostics", diagnostics)


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
    )

    bounds = authority_field_bounds(RESULT_JSON_POLICY)
    # 辿ってよい量は、置き換えた record が書かれる出力 field の上限（schema。予算を無効にした
    # policy でも有限）
    work = JsonBudget(bounds["unknown_reasons"].max_bytes + bounds["unknown_recovery_actions"].max_bytes)

    reasons = live_values.attribute(result, "unknown_reasons")
    if _truthy(reasons):
        count = live_values.size(reasons)
        keep = count
        if authority_projects_reasons:
            # 診断にしか使わない legacy reason: canonical reason の行数の上限（schema）まで残す
            limit = bounds["unknown_reasons"].max_rows
            if count > limit:
                live_values.set_state(result, "legacy_reason_overflow", count - limit)
                keep = limit
        else:
            limit = _schema_row_limit(bounds, "unknown_reasons", UNKNOWN_REASON_ROW)
            if count > limit:
                _raise_over_schema("unknown_reasons", count, limit)
        live_values.set_state(result, "unknown_reasons", _finitized_reasons(reasons, keep, work=work))
    actions = live_values.attribute(result, "unknown_recovery_actions")
    if _truthy(actions):
        count = live_values.size(actions)
        limit = _schema_row_limit(bounds, "unknown_recovery_actions", UNKNOWN_RECOVERY_ACTION_ROW)
        if count > limit:
            _raise_over_schema("unknown_recovery_actions", count, limit)
        live_values.set_state(result, "unknown_recovery_actions", _finitized_actions(actions, work=work))


def _schema_row_limit(bounds: Mapping[str, Any], key: str, row: Any) -> int:
    """出力 schema の field の上限と行の下限から導く、その field に入り得る行数の上限。"""

    from scripts.function_tracer_pcode.core.json_encoding import max_rows_within, row_min_bytes

    return max_rows_within(bounds[key].max_bytes, row_min_bytes(row, RESULT_JSON_POLICY))


def _raise_over_schema(key: str, count: int, limit: int) -> None:
    raise_expression_size_budget_exceeded(
        BudgetKind.SERIALIZATION_BYTES,
        observed=count,
        limit=limit,
        site=PREPARATION_SITE,
        target_key=("result_payload", key, "rows"),
        evidence=(f"field={key}", f"rows={count}", f"schema_max_rows={limit}"),
    )


def _finitized_reasons(reasons: Any, keep: int, *, work: JsonBudget) -> List[Any]:
    """先頭 `keep` 件の legacy reason（`UnknownReasonRecord` は重い field を有界にした record）。"""

    from scripts.function_tracer_pcode.checker.unknown_reason import (
        UnknownReasonRecord,
        finitize_unknown_reason_record,
    )

    kept: List[Any] = []
    taken = 0
    for item in live_values.elements_of(reasons):
        if taken >= keep:
            break
        taken += 1
        if live_values.is_kind(item, UnknownReasonRecord):
            kept.append(finitize_unknown_reason_record(item, work=work))
        else:
            kept.append(item)
    return kept


def _finitized_actions(actions: Any, *, work: JsonBudget) -> List[Any]:
    """recovery action（`UnknownRecoveryAction` は重い field を有界にした record）。"""

    from scripts.function_tracer_pcode.checker.unknown_reason import (
        UnknownRecoveryAction,
        finitize_unknown_recovery_action,
    )

    kept: List[Any] = []
    for item in live_values.elements_of(actions):
        if live_values.is_kind(item, UnknownRecoveryAction):
            kept.append(finitize_unknown_recovery_action(item, work=work))
        else:
            kept.append(item)
    return kept


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
            # 切り詰めてはいけない field（B）の読み方の値（`read_source` は `read` の値そのもの）
            source = OutputField.read_source(FIELD_BY_KEY[key], result, None)
            json_encoding.RESULT_JSON_POLICY.measure(source, max_bytes=bound.max_bytes)
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
    policy = active_budget_policy()
    preparer = OutputPreparer(policy)
    options = OutputOptions.for_result(result, save_formula=save_formula)
    identities = live_values.attribute(checker, "_active_binary_content_identities")
    identities = tuple(live_values.elements_of(identities)) if _truthy(identities) else (None, None)
    authority_projects_reasons = (
        live_values.attribute(checker, "v2_dual_write_pilot_connector") is not None
    )
    gate = _PairFailureGate(checker, function_name1, function_name2, start_time)

    try:
        _finitize_and_check(result, authority_projects_reasons=authority_projects_reasons)
        prepared = preparer.prepare(result, options, binary_identities=identities)
    except (AnalysisLimitation, JsonValueRejected) as exc:
        if isinstance(exc, JsonValueRejected):
            _record_preparation_bug(exc)
        result = gate.apply(result)
        try:
            _finitize_and_check(result, authority_projects_reasons=authority_projects_reasons)
            prepared = preparer.prepare(result, options, binary_identities=identities)
        except (AnalysisLimitation, JsonValueRejected) as again:
            _record_preparation_bug(again)
            result = gate.apply(result)
            try:
                finitize_legacy_reasons(result, authority_projects_reasons=True)
            except AnalysisLimitation as third:  # pragma: no cover - 小さい結果は収まる
                _record_preparation_bug(third)
            prepared = preparer.prepare(
                result, options, strict=False, binary_identities=identities,
            )
    _attach_budget_diagnostics(result, prepared, policy)
    live_values.set_state(result, "prepared_semantic_payload", prepared)
    return result


def _finitize_and_check(result: Any, *, authority_projects_reasons: bool) -> None:
    finitize_legacy_reasons(result, authority_projects_reasons=authority_projects_reasons)
    check_prepared_field_bounds(result, authority_projects_reasons=authority_projects_reasons)


class _PairFailureGate:
    """準備が収まらない / JSON にならない結果を、pair の失敗の変換（G4-a と同じ）で作り直す。"""

    __slots__ = ("checker", "function_name1", "function_name2", "start_time")

    def __init__(self, checker: Any, function_name1: str, function_name2: str, start_time: float) -> None:
        self.checker = checker
        self.function_name1 = function_name1
        self.function_name2 = function_name2
        self.start_time = start_time

    def apply(self, current: Any) -> Any:
        from scripts.function_tracer_pcode.checker.pair_execution import (
            apply_pair_failure_gate,
        )

        return apply_pair_failure_gate(
            self.checker,
            current,
            function_name1=self.function_name1,
            function_name2=self.function_name2,
            start_time=self.start_time,
        )


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

    prepared = live_values.attribute(result, "prepared_semantic_payload")
    if prepared is None:
        policy = fallback_policy if fallback_policy is not None else active_budget_policy()
        return OutputPreparer(policy).prepare(result)
    if type(prepared) is not PreparedSemanticPayload:
        raise TypeError("result.prepared_semantic_payload must be a PreparedSemanticPayload")
    return prepared


def prepared_smt_formula(result: Any, *, requested: bool) -> PreparedArtifact:
    """`--save-formula` が書く SMT 式（準備済みの成果物だけを返す）。頼まれていなければ何もしない。

    準備済みでない結果（pair 境界を通らずに組んだ結果）の式も、同じ owner が同じ上限で今準備する
    （生の属性をそのまま書かない。式にならない値・読めない値・上限の外は保存しない。authority の
    後なので失敗にしない）。
    """

    if requested is not True:
        return PreparedArtifact(None)
    prepared = live_values.attribute(result, "prepared_semantic_payload")
    if prepared is None:
        options = OutputOptions(include_debug_trace=False, include_smt_formula=True)
        try:
            return OutputPreparer(active_budget_policy())._prepare_smt_formula(result, options)
        except (JsonValueRejected, TypeError):
            return PreparedArtifact(None)
    if type(prepared) is not PreparedSemanticPayload:
        raise TypeError("result.prepared_semantic_payload must be a PreparedSemanticPayload")
    return prepared.smt_formula


#: `_ordered` が「その field は無い」ことを知る印
_NO_PART = object()


def _ordered(parts: Dict[str, Any]) -> Dict[str, Any]:
    """field の値を出力の key 順に並べ直す（並びは `RESULT_FIELDS` の固定の key で決める）。"""

    order = _field_order()
    ordered: Dict[str, Any] = {}
    for key in sorted(order, key=order.__getitem__):
        value = parts.get(key, _NO_PART)
        if value is not _NO_PART:
            ordered[key] = value
    if len(ordered) != live_values.size(parts):
        raise KeyError("the result payload has a key outside RESULT_FIELDS")
    return ordered


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


def _budget_total(members: Any) -> int:
    """object の勘定の今の byte 数（`JsonObjectBudget.total_bytes` を plain な `int` で読む）。"""

    return live_values.as_int(live_values.attribute(members, "total_bytes"))


def _budget_limit(members: Any) -> Optional[int]:
    return _optional_int(live_values.attribute(members, "max_bytes"))


def _object_budget(members: Any) -> JsonObjectBudget:
    """組んだ preimage の勘定（`JsonObjectBudget` そのもの）。"""

    if type(members) is not JsonObjectBudget:
        raise TypeError("the composed preimage needs its JsonObjectBudget")
    return members


def _checked_payload(prepared: Any) -> PreparedSemanticPayload:
    if type(prepared) is not PreparedSemanticPayload:
        raise TypeError("result.prepared_semantic_payload must be a PreparedSemanticPayload")
    return prepared


def _plan_note(prepared: Any) -> str:
    """違反の文に添える準備の内訳（`prepared N, headroom M`）。"""

    plan = _checked_payload(prepared).payload_plan()
    return f"prepared {plan.prepared_size()}, headroom {plan.headroom()}"


def _violation(
    message: str, members: Any, consumed: int = 0, *, field_bound: Optional[int] = None,
) -> OutputEnvelopeInvariantViolation:
    if field_bound is not None:
        # field の schema の上限を破った: 上限と要求量は field の値（envelope 全体ではない）
        return OutputEnvelopeInvariantViolation(message, max_bytes=field_bound, requested_bytes=consumed)
    return OutputEnvelopeInvariantViolation(
        message,
        max_bytes=_budget_limit(members) or 0,
        requested_bytes=_budget_total(members) + consumed,
    )


def _prepare_after_authority(
    item: OutputField,
    result: Any,
    context: PreparationContext,
    prepared: PreparedSemanticPayload,
    *,
    field_max_bytes: Optional[int] = None,
    source: Any = None,
) -> Optional[PreparedField]:
    # `item` は `RESULT_FIELDS` の行（package の定数）
    members = context.members
    try:
        if source is None:
            return OutputField.prepare(item, result, context, field_max_bytes=field_max_bytes)
        return OutputField.prepare_source(item, source, context, field_max_bytes=field_max_bytes)
    except JsonBudgetExhausted as exc:
        consumed = exc.consumed_bytes
        if field_max_bytes is not None and (
            members.remaining_for(item.key) is None
            or field_max_bytes <= members.remaining_for(item.key)
        ):
            raise _violation(
                f"{item.key} exceeds its output schema bound of {field_max_bytes} bytes",
                members, consumed, field_bound=field_max_bytes,
            ) from exc
        raise _violation(
            f"{item.key} must not be truncated but does not fit the envelope "
            f"({_plan_note(prepared)})",
            members, consumed,
        ) from exc
    except JsonValueRejected as exc:
        raise _violation(f"{item.key} is not JSON: {exc}", members) from exc


@dataclass(frozen=True)
class AuthorityDecisionEnvelope:
    """B: authority が確定した field。authority の attach_* が書いた値だけを読む。

    authority 確定後に同じ `JsonEncodingPolicy.prepare` で canonical にする（切り
    詰めない: 収まらない・JSON にならないのは出力契約の違反）。A の同名 field で
    上書きすることは無い（`RESULT_FIELDS` が所有者を 1 つに決める）。
    """

    fields: Tuple[PreparedField, ...]

    @staticmethod
    def prepare(
        result: Any, context: PreparationContext, prepared: PreparedSemanticPayload,
    ) -> "AuthorityDecisionEnvelope":
        from scripts.function_tracer_pcode.checker.output_schema import (
            OutputSchemaMissing,
            authority_field_bounds,
        )

        bounds = authority_field_bounds(context.encoding)
        rows = []
        present_in_group: Dict[str, str] = {}
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
                group = bound.exclusive_group
                if group is not None and row.json is not None and row.json.value() is not None:
                    # headroom は組の中の最大だけを予約している: 2 つ目は出力の契約違反
                    if group in present_in_group:
                        raise _violation(
                            f"{item.key} and {present_in_group[group]} share the exclusive output "
                            f"group {group!r}", context.members,
                        )
                    present_in_group[group] = item.key
                rows.append(row)
        return AuthorityDecisionEnvelope(tuple(rows))


@dataclass(frozen=True)
class OutputMetadata:
    """C: 判定に関わらない field（切り詰めてよいものは marker、いけないものは違反）。"""

    fields: Tuple[PreparedField, ...]

    @property
    def truncated(self) -> Tuple[str, ...]:
        return tuple(row.field_key() for row in self.fields if row.field_shape() != "json")

    @staticmethod
    def prepare(
        result: Any, context: PreparationContext, prepared: PreparedSemanticPayload,
    ) -> "OutputMetadata":
        """C を準備する。

        * 切り詰めてはいけない field を先に、出力 schema の上限の中で準備する（超えれば違反）。
        * 切り詰めてよい診断は、先に準備した診断の本体が後の field の場所を使い切らないように、
          field ごとの場所を予約してから準備する: field ごとに marker の大きさの上限（schema の
          `truncation_marker_max_bytes`。headroom・組み直しの見積もりと同じ値）の中で本体を試す。収まる
          field は本体で確定し（切り詰めても byte は減らない）、その大きさを予約する。収まらない
          field は marker の大きさを予約し、順に予約を外して残りの予算で本体（入らなければ
          marker）を準備する。予約の和が入らなければ出力の契約違反（headroom は marker の上限の和
          を含むので、契約どおりの設定では起きない）。どの field も黙って消えない。
        """

        from scripts.function_tracer_pcode.checker.output_schema import (
            metadata_field_bounds,
            truncation_marker_max_bytes,
        )

        bounds = metadata_field_bounds(context.encoding)
        members = context.members
        encoding = context.encoding
        rows: Dict[str, PreparedField] = {}
        large = []
        small_keys: List[str] = []
        order = []
        for item in _rows(FieldOwner.METADATA, first=Overflow.INVARIANT):
            if item.overflow is not Overflow.TRUNCATE:
                row = _prepare_after_authority(
                    item, result, context, prepared, field_max_bytes=bounds[item.key].max_bytes,
                )
                if row is not None:
                    rows[item.key] = row
                    order.append(item.key)
                continue
            # `item` は `RESULT_FIELDS` の行（package の定数）
            source = OutputField.read_source(item, result, context.options)
            if source is ABSENT:
                continue
            order.append(item.key)
            # 予約・組み直しの見積もり（`freeable`）・schema の headroom は同じ 1 つの上限
            marker_bytes = truncation_marker_max_bytes(encoding, item.key)
            try:
                if type(source) is _ReadFailed:
                    raise source.rejected
                small = _prepare_json(encoding, source, max_bytes=marker_bytes)
            except (JsonBudgetExhausted, JsonValueRejected):
                large.append(item)
                members.reserve(item.key, marker_bytes)
                continue
            rows[item.key] = PreparedField(item.key, small, "json")
            small_keys.append(item.key)
            members.reserve(item.key, small.encoded_bytes)
        room = members.room()
        if room is not None and room < 0:
            raise _violation(
                f"the truncatable metadata does not fit even as markers ({_plan_note(prepared)})",
                members,
            )
        for item in large:
            members.release_reservation(item.key)
            # source は読み直す（1 回目の試しで遅延列を辿った）
            row = _prepare_after_authority(item, result, context, prepared)
            if row is not None:
                rows[item.key] = row
        # 予約で場所を取っていた小さい field を、予約を外して member として足す
        for key in small_keys:
            members.release_reservation(key)
            members.add(key, rows[key].encoded_bytes)
        return OutputMetadata(tuple(rows[key] for key in order if key in rows))


def _compose_members(
    result: Any,
    prepared: PreparedSemanticPayload,
    members: JsonObjectBudget,
    parts: Dict[str, Any],
) -> Tuple[Tuple[str, ...], int]:
    """B と C を `members` の残り予算まで準備して `parts` へ置く。

    切り詰めた C と、切り詰めれば空けられる byte の上限（本体を出した TRUNCATE の C の、
    本体と marker の上限の差の和）を返す。
    """

    # option は準備済みの payload から plain な値として読み直す（context は package の値だけ）
    context = PreparationContext(_checked_payload(prepared).output_options(), members)
    authority = AuthorityDecisionEnvelope.prepare(result, context, prepared)
    metadata = OutputMetadata.prepare(result, context, prepared)
    for row in authority.fields + metadata.fields:
        if row.json is not None:
            parts[row.key] = row.json.value()
    from scripts.function_tracer_pcode.checker.output_schema import truncation_marker_max_bytes

    freeable = 0
    for row in metadata.fields:
        if row.json is not None and row.shape == "json" and _TRUNCATABLE_METADATA.get(row.key):
            # 切り詰めても marker（予約と同じ上限）は残る
            freeable += max(0, row.encoded_bytes - truncation_marker_max_bytes(members.policy, row.key))
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

    # 最終 envelope が読む値（型を確かめ、plain な値として読み直す）

    def payload_plan(self) -> "SerializationPlan":
        return _checked_payload(self.prepared).payload_plan()

    def preimage(self) -> Dict[str, Any]:
        payload = self.payload
        if type(payload) is not dict:
            raise TypeError("the composed preimage needs its payload dict")
        return payload

    def budget(self) -> JsonObjectBudget:
        return _object_budget(self.members)

    def truncated_fields(self) -> Tuple[str, ...]:
        return tuple(live_values.as_str(key) for key in live_values.elements_of(self.truncated))

    def freeable(self) -> int:
        return live_values.as_int(self.freeable_bytes)


def compose_result_preimage(
    result: Any, *, fallback_policy: Optional[BudgetPolicy] = None, bundle_reserve: Optional[int] = None,
) -> ComposedPreimage:
    """A + B + C の preimage を上限の中で組む（最終 envelope と `to_dict()` の共通の本体）。

    `bundle_reserve` を渡すと、封印（bundle）の値の byte をその分だけ先に空けてから B / C を
    準備する（切り詰めてよい C が先に marker になる）。
    """

    prepared = _checked_payload(prepared_payload_for(result, fallback_policy=fallback_policy))
    plan = prepared.payload_plan()
    limit = plan.limit()
    members = JsonObjectBudget(plan.encoder(), limit)
    parts: Dict[str, Any] = {}
    for item in live_values.elements_of(prepared.fields):
        if type(item) is not PreparedField:
            raise TypeError("prepared payload fields must be PreparedField")
        if not item.has_json():
            continue
        key = item.field_key()
        members.add(key, item.encoded_bytes)
        parts[key] = item.json_value()
    if limit is not None and members.total_bytes > limit:
        raise _violation(
            "prepared output exceeded the envelope before authority fields "
            f"({members.total_bytes} > {limit} bytes; headroom {plan.headroom()})",
            members,
        )
    if bundle_reserve is not None:
        members.reserve(BUNDLE_KEY, live_values.as_int(bundle_reserve))
    truncated, freeable = _compose_members(result, prepared, members, parts)
    members.release_reservation()
    return ComposedPreimage(prepared, _ordered(parts), members, tuple(truncated), freeable)


#: 1 つの最終 envelope が封印する回数の上限（組み直すときだけ 2 回目。`finalize_result_envelope`）
SEALS_PER_ENVELOPE = 2


def envelope_seal_work() -> Any:
    """最終 envelope 1 つの封印の作業量（Issue #110 の `SealWork`）。

    封印を `SEALS_PER_ENVELOPE` 回と、その envelope の永続化の検証 1 回の作業量（上限は authority の
    event の契約と結果の preimage の上限だけから決まる: 契約の内側の入力は作業量の不足で失敗しない）。
    envelope 1 つにつき 1 つ作り、その envelope の封印と永続化だけに使う（1 つの結果が作る envelope は
    確定した判定の envelope と、出力の失敗の ERROR の envelope の高々 2 つ + 最後の固定の文の envelope）。
    """

    from scripts.function_tracer_pcode.authority.seal_work import SealWorkBudget

    return SealWorkBudget.for_result(passes=SEALS_PER_ENVELOPE + 1)


class AuthoritySeal:
    """最終 envelope の封印（canonical result finalization bundle）を作る authority の builder。

    `seal(preimage, work=...)` は authority の `build_canonical_result_finalization_bundle` を呼ぶ。
    sealed event stream の codec・replay・digest の仕事は、呼ぶ側の有限の作業量 `work`（Issue #110 の
    `SealWork`）の中でだけ行う（各段を実行する前に数え、超えれば `BundleWorkExceeded`: 部分的な封印を
    返さない）。field に callable を持たない。本 module が保証するのは、呼ぶのは envelope 1 つを作るごとに
    高々 `SEALS_PER_ENVELOPE` 回、作った封印は残りの予算の中でしか写さない、超えれば durable な ERROR。

    production の型はこの型そのもの（subclass を作らない: architecture test の J14。
    `finalize_result_envelope` は型を `is` で確かめる）。
    """

    __slots__ = ("evidence", "session")

    def __init__(self, *, evidence: Any, session: Any) -> None:
        self.evidence = evidence
        self.session = session

    def seal(self, preimage: Mapping[str, Any], *, work: Any) -> Mapping[str, Any]:
        from scripts.function_tracer_pcode.authority.decision.canonical_result import (
            build_canonical_result_finalization_bundle,
        )

        return build_canonical_result_finalization_bundle(
            result_payload_preimage=preimage, evidence=self.evidence, session=self.session,
            work=work,
        )


def build_final_result_envelope(
    result: Any,
    *,
    seal: Optional["AuthoritySeal"] = None,
    work: Any = None,
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

    封印を **組み立てる** 作業（authority の event stream の codec・replay）は `work`（この envelope の
    `envelope_seal_work()`）の中でだけ行う（Issue #110 の契約: event の件数と大きさは authority の
    event の契約が作る時点で抑え、封印の各段は実行する前に数える）。本 function が有界にするのは、
    封印を呼ぶ回数・組み立てた封印を出力へ写す作業・最終 JSON の大きさ。
    """

    return finalize_result_envelope(
        compose_result_preimage(result, fallback_policy=fallback_policy), seal=seal, work=work,
        recompose_from=result, fallback_policy=fallback_policy,
    )


def finalize_result_envelope(
    composed: ComposedPreimage,
    *,
    seal: Optional["AuthoritySeal"] = None,
    work: Any = None,
    recompose_from: Any = None,
    fallback_policy: Optional[BudgetPolicy] = None,
) -> FinalResultEnvelope:
    """組んだ preimage に封印を足し、契約の上限で書く（`build_final_result_envelope` の後半）。

    封印が残りに収まらず、preimage に切り詰めてよい診断（C）があれば、封印の大きさ（契約の
    上限の中で数えた値）を先に空けて `recompose_from`（preimage を組んだ結果）から組み直し
    （`compose_result_preimage(..., bundle_reserve=...)`。callback は受けない）、封印し直す。封印は preimage の
    digest を持つので、preimage が変われば作り直す。封印の大きさは preimage の中身に依存し得る
    ので、作り直した封印も残りの予算の中で準備し直し、それでも収まらなければ出力の契約違反。
    """

    if type(composed) is not ComposedPreimage:
        raise TypeError("the final envelope is built from a ComposedPreimage")
    plan = composed.payload_plan()
    preimage = composed.preimage()
    members = composed.budget()
    truncated = composed.truncated_fields()
    encoding = plan.encoder()
    limit = plan.limit()
    preimage_bytes = _budget_total(members)
    payload = preimage
    total = preimage_bytes
    if seal is not None:
        if type(seal) is not AuthoritySeal:
            raise TypeError("the final envelope is sealed only by an AuthoritySeal")
        if work is None:
            raise TypeError("a sealed final envelope needs its seal work (envelope_seal_work())")
        room = members.remaining_for(BUNDLE_KEY)
        # 封印を写す上限: 残り、組み直せるなら残り + 切り詰められる byte（1 回の準備で、入るか・
        # 組み直しに要る大きさかが分かる。封印を 3 回作らない）
        freeable = composed.freeable()
        can_recompose = recompose_from is not None and freeable > 0 and room is not None
        reach = room + freeable if can_recompose else room
        try:
            bundle = encoding.prepare(seal.seal(preimage, work=work), max_bytes=reach)
        except JsonBudgetExhausted as exc:
            raise _violation(
                f"{BUNDLE_KEY} does not fit the rest of the envelope "
                f"(> {reach} bytes after a {preimage_bytes}-byte preimage)",
                members,
            ) from exc
        except JsonValueRejected as exc:
            raise _violation(f"{BUNDLE_KEY} is not JSON: {exc}", members) from exc
        bundle_bytes = live_values.as_int(bundle.encoded_bytes)
        if room is not None and bundle_bytes > room:
            # 切り詰めてよい診断が場所を取っている: 封印の大きさを先に空けて組み直し、新しい
            # preimage を封印し直す（封印は preimage の digest を持つ。2 回目の封印）
            composed = compose_result_preimage(
                recompose_from, fallback_policy=fallback_policy, bundle_reserve=bundle_bytes,
            )
            plan = composed.payload_plan()
            preimage = composed.preimage()
            members = composed.budget()
            truncated = composed.truncated_fields()
            preimage_bytes = _budget_total(members)
            room = members.remaining_for(BUNDLE_KEY)
            try:
                bundle = encoding.prepare(seal.seal(preimage, work=work), max_bytes=room)
            except JsonBudgetExhausted as exc:
                raise _violation(
                    f"{BUNDLE_KEY} does not fit the rest of the envelope "
                    f"(> {room} bytes after a {preimage_bytes}-byte preimage)",
                    members,
                ) from exc
            except JsonValueRejected as exc:
                raise _violation(f"{BUNDLE_KEY} is not JSON: {exc}", members) from exc
            bundle_bytes = live_values.as_int(bundle.encoded_bytes)
        payload = {**preimage}
        payload[BUNDLE_KEY] = bundle.value()
        payload = _ordered(payload)
        members.add(BUNDLE_KEY, bundle_bytes)
        total = _budget_total(members)
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
    "output_contract_policy",
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
    "AuthoritySeal",
    "SEALS_PER_ENVELOPE",
    "envelope_seal_work",
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
