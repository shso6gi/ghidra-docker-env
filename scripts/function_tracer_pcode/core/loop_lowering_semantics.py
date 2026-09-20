# -*- coding: utf-8 -*-
"""loop lowering が要る意味だけを取り出した不変な投影（Issue #22 PR-22-B）。

**loop summary ref の schema を読むのはここだけ**。SMT renderer
（`core/render_smt/loop_lowering.py`）は「どの lowering か」「厳密 lowering が
可能か」「その parameter は何か」だけを見て、`induction_step` や
`side_effect_profile.context_calls` といった ref の field 名を知らない。

なぜ分けるか: 従来は renderer が `expr.runtime_ref` を `isinstance` で 4 種類に
振り分け、`getattr(ref, "…", 既定値)` で 20 個近い field を直接読んでいた。
loop summary 側に field が増減すると renderer が黙って既定値に落ち、SMT 関数名
と厳密 lowering の可否が「renderer がどの field 名を知っていたか」で決まって
いた。判断をこちらへ移すと:

* 新しい loop summary 種別を足すときに触るのは、ここと `LoweringKind` だけ
* 厳密 lowering の可否（= 健全性に効く判断）が 1 箇所で読める
* renderer は凍結済みの値だけを見るので、描画のたびに生 ref を読み直さない

ここが返す値はすべて不変。式そのもの（residue の bias 項など）は renderer が
部分式として描画する必要があるので値として持つ — 公開済みの式は不変なので、
これは生 object を持ち出していることにはならない。
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, NamedTuple, Optional, Tuple

from scripts.function_tracer_pcode.core.runtime_refs import (
    CountedLoopSummaryRef,
    CountedStateTransitionLoopSummaryRef,
    ReadonlyReductionRef,
    StateTransitionLoopSummaryRef,
)


class LoweringKind(Enum):
    """この式を SMT へ落とすときに使う lowering の種別。

    `NONE` は「loop lowering の対象ではない」。renderer はこの列挙だけで分岐し、
    ref の class を見ない。
    """

    NONE = "none"
    READONLY_REDUCTION = "readonly_reduction"
    COUNTED_LOOP_SUM = "counted_loop_sum"
    STATE_TRANSITION_LOOP_COUNT = "state_transition_loop_count"
    COUNTED_STATE_TRANSITION_VALUE = "counted_state_transition_value"


class ResidueCase(NamedTuple):
    """counted loop sum の剰余ごとの寄与 `(modulus, residue, coefficient, bias)`。"""

    modulus: int
    residue: int
    coefficient: int
    bias: int


class ResidueBiasTerm(NamedTuple):
    """剰余ごとに 1 回ずつ足される式の項。

    `bias_expression` は公開済みの式。renderer が部分式として描画する。
    """

    modulus: int
    residue: int
    bias_expression: Any


@dataclass(frozen=True)
class LoopLoweringSemantics:
    """loop lowering に必要な意味を凍結時に確定させた値。

    renderer はこの値だけを読む。ここに無い情報が要るようになったら、
    field を 1 つ足すのが正しい（renderer 側で生 ref を読み直さない）。
    """

    #: どの lowering か
    kind: LoweringKind
    #: SMT function 名に使う安定な identity（`None` なら identity を出せない）
    identity: Optional[Tuple[Any, ...]]
    #: 厳密 lowering（未解釈関数ではなく閉じた式）へ落とせるか
    exact_lowering_available: bool
    #: reduction の種類名（`READONLY_REDUCTION` のときだけ意味を持つ）
    reduction_kind: Optional[str]
    #: 反復の符号性（比較・拡張の符号を決める）
    signed_loop: bool
    #: 帰納変数の 1 反復あたりの増分（`COUNTED_LOOP_SUM`）
    induction_step: int
    #: 剰余ごとの寄与（`COUNTED_LOOP_SUM`）
    residue_cases: Tuple[ResidueCase, ...]
    #: 剰余ごとの式の項（`COUNTED_LOOP_SUM`）
    residue_bias_terms: Tuple[ResidueBiasTerm, ...]
    #: 状態遷移が定数倍のとき、その倍率（`COUNTED_STATE_TRANSITION_VALUE`）
    exact_multiplier: Optional[int]
    #: loop 本体の副作用に証明が要るか（要るなら厳密 lowering はしない）
    effect_proof_required: bool
    #: loop の経路に証明が要るか
    path_proof_required: bool


ABSENT_LOWERING = LoopLoweringSemantics(
    kind=LoweringKind.NONE,
    identity=None,
    exact_lowering_available=False,
    reduction_kind=None,
    signed_loop=False,
    induction_step=0,
    residue_cases=(),
    residue_bias_terms=(),
    exact_multiplier=None,
    effect_proof_required=False,
    path_proof_required=False,
)


def project_loop_lowering(
    expr: Any, runtime_ref: Any, *, identity: Optional[Tuple[Any, ...]]
) -> LoopLoweringSemantics:
    """生の loop summary ref を lowering の意味へ落とす（凍結時に 1 回）。

    `identity` は `semantic_projection` が決めた SMT function identity。
    ここで作り直すと「identity をどう決めるか」の答えが 2 つになるので受け取る。
    """

    if runtime_ref is None:
        return ABSENT_LOWERING
    if isinstance(runtime_ref, ReadonlyReductionRef):
        return _readonly_reduction_semantics(runtime_ref, identity)
    if isinstance(runtime_ref, CountedLoopSummaryRef):
        return _counted_loop_sum_semantics(expr, runtime_ref, identity)
    if isinstance(runtime_ref, CountedStateTransitionLoopSummaryRef):
        return _counted_state_transition_semantics(runtime_ref, identity)
    if isinstance(runtime_ref, StateTransitionLoopSummaryRef):
        return _state_transition_count_semantics(runtime_ref, identity)
    return ABSENT_LOWERING


# ---------------------------------------------------------------------------
# 種別ごとの読み取り
# ---------------------------------------------------------------------------


def _readonly_reduction_semantics(
    runtime_ref: ReadonlyReductionRef, identity: Optional[Tuple[Any, ...]]
) -> LoopLoweringSemantics:
    effect_required, path_required = _loop_summary_proof_obligations(runtime_ref)
    return LoopLoweringSemantics(
        kind=LoweringKind.READONLY_REDUCTION,
        identity=identity,
        # readonly reduction は未解釈関数で表す（閉じた式へは落とさない）。
        exact_lowering_available=False,
        reduction_kind=str(runtime_ref.reduction_kind or "sum"),
        signed_loop=bool(runtime_ref.signed_counter),
        induction_step=0,
        residue_cases=(),
        residue_bias_terms=(),
        exact_multiplier=None,
        effect_proof_required=effect_required,
        path_proof_required=path_required,
    )


def _state_transition_count_semantics(
    runtime_ref: StateTransitionLoopSummaryRef, identity: Optional[Tuple[Any, ...]]
) -> LoopLoweringSemantics:
    effect_required, path_required = _loop_summary_proof_obligations(runtime_ref)
    return LoopLoweringSemantics(
        kind=LoweringKind.STATE_TRANSITION_LOOP_COUNT,
        identity=identity,
        exact_lowering_available=False,
        reduction_kind=None,
        signed_loop=False,
        induction_step=0,
        residue_cases=(),
        residue_bias_terms=(),
        exact_multiplier=None,
        effect_proof_required=effect_required,
        path_proof_required=path_required,
    )


def _counted_loop_sum_semantics(
    expr: Any, runtime_ref: CountedLoopSummaryRef, identity: Optional[Tuple[Any, ...]]
) -> LoopLoweringSemantics:
    residue_cases = tuple(
        ResidueCase(int(modulus), int(residue), int(coefficient), int(bias))
        for modulus, residue, coefficient, bias in (runtime_ref.residue_cases or ())
    )
    residue_bias_terms = tuple(
        ResidueBiasTerm(int(modulus), int(residue), bias_expression)
        for modulus, residue, bias_expression in (runtime_ref.residue_bias_terms or ())
    )
    induction_step = int(runtime_ref.induction_step or 0)
    effect_required, path_required = _loop_summary_proof_obligations(runtime_ref)
    return LoopLoweringSemantics(
        kind=LoweringKind.COUNTED_LOOP_SUM,
        identity=identity,
        exact_lowering_available=_counted_loop_sum_is_exact(
            expr, induction_step, residue_cases
        ),
        reduction_kind=None,
        signed_loop=bool(runtime_ref.signed_loop),
        induction_step=induction_step,
        residue_cases=residue_cases,
        residue_bias_terms=residue_bias_terms,
        exact_multiplier=None,
        effect_proof_required=effect_required,
        path_proof_required=path_required,
    )


def _counted_loop_sum_is_exact(
    expr: Any, induction_step: int, residue_cases: Tuple[ResidueCase, ...]
) -> bool:
    """閉じた式へ落とせる剰余系かどうか。

    step が 1 なら剰余は 2 冪でなければ位取り演算で表せない。step が 1 でない
    場合は剰余分解を扱わない（modulus 1 のみ）。
    """

    if len(tuple(getattr(expr, "operands", None) or ())) != 3:
        return False
    if induction_step == 0 or not residue_cases:
        return False
    if induction_step != 1:
        return all(case.modulus == 1 for case in residue_cases)
    for case in residue_cases:
        if case.modulus <= 1:
            continue
        mask = case.modulus - 1
        if mask <= 0 or (mask & (mask + 1)) != 0:
            return False
    return True


def _counted_state_transition_semantics(
    runtime_ref: CountedStateTransitionLoopSummaryRef,
    identity: Optional[Tuple[Any, ...]],
) -> LoopLoweringSemantics:
    effect_required, path_required = _loop_summary_proof_obligations(runtime_ref)
    multiplier = _counted_state_transition_multiplier(runtime_ref)
    return LoopLoweringSemantics(
        kind=LoweringKind.COUNTED_STATE_TRANSITION_VALUE,
        identity=identity,
        exact_lowering_available=multiplier is not None,
        reduction_kind=None,
        signed_loop=bool(runtime_ref.signed_loop),
        induction_step=0,
        residue_cases=(),
        residue_bias_terms=(),
        exact_multiplier=multiplier,
        effect_proof_required=effect_required,
        path_proof_required=path_required,
    )


def _counted_state_transition_multiplier(
    runtime_ref: CountedStateTransitionLoopSummaryRef,
) -> Optional[int]:
    """状態遷移が `state * 定数` の 1 経路だけなら、その定数。

    厳密 lowering の可否そのものなので、緩めると偽の EQUIVALENT に繋がる。
    条件を 1 つでも確かめられなければ `None`（= 未解釈関数へ退避）。
    """

    if _constant_int(runtime_ref.step_expr) != 1:
        return None
    if not _side_effect_profile_is_pure_enough(runtime_ref.side_effect_profile):
        return None
    transition_cases = tuple(runtime_ref.transition_cases or ())
    if len(transition_cases) != 1:
        return None
    case = transition_cases[0]
    if not isinstance(case, tuple) or len(case) != 2:
        return None
    condition_signature, transition_signature = case
    if condition_signature not in {(), (("none",),), None}:
        return None
    transition_expr = runtime_ref.transition_expr
    state_placeholder = runtime_ref.state_placeholder
    if transition_expr is None or state_placeholder is None:
        return None
    if not _signature_matches_expression(transition_signature, transition_expr):
        return None
    expr_type = getattr(transition_expr, "expr_type", None)
    if expr_type is None or expr_type != expr_type.__class__.BINARY_OP:
        return None
    if getattr(transition_expr, "operator", None) != "INT_MULT":
        return None
    operands = tuple(getattr(transition_expr, "operands", None) or ())
    if len(operands) != 2:
        return None
    for maybe_state, maybe_constant in ((operands[0], operands[1]), (operands[1], operands[0])):
        if not _expressions_equal(maybe_state, state_placeholder):
            continue
        multiplier = _constant_int(maybe_constant)
        if multiplier is None:
            return None
        return int(multiplier)
    return None


def _side_effect_profile_is_pure_enough(profile: Any) -> bool:
    """厳密 lowering してよい副作用 profile か。

    「条件分岐 guard だけ」までは許す — guard は経路条件であって状態を変えない。
    それ以外の記述子が 1 つでもあれば、閉じた式は loop 本体を表していない。
    """

    if profile is None:
        return False
    requires_effect_proof = getattr(profile, "requires_effect_proof", None)
    if callable(requires_effect_proof) and requires_effect_proof():
        return False
    for flag in (
        "memory_reads",
        "memory_writes",
        "calls",
        "escapes",
        "context_memory_writes",
        "context_calls",
        "context_escapes",
        "context_conditional_guards",
    ):
        if bool(getattr(profile, flag, False)):
            return False
    if tuple(getattr(profile, "context_descriptors", ()) or ()):
        return False
    effect_descriptors = tuple(getattr(profile, "effect_descriptors", ()) or ())
    return all(
        getattr(effect, "kind", None) == "conditional_guard"
        for effect in effect_descriptors
    )


def _loop_summary_proof_obligations(runtime_ref: Any) -> Tuple[bool, bool]:
    """この ref が抱える loop summary に副作用/経路の証明義務があるか。"""

    loop_summary = getattr(runtime_ref, "loop_summary", None)
    if loop_summary is None:
        return (False, False)
    return (
        _proof_obligation(loop_summary, "requires_effect_proof"),
        _proof_obligation(loop_summary, "requires_path_proof"),
    )


def _proof_obligation(loop_summary: Any, method_name: str) -> bool:
    method = getattr(loop_summary, method_name, None)
    return bool(callable(method) and method())


# ---------------------------------------------------------------------------
# 式の読み取り（ここで使う分だけ。renderer の幅計算には依存しない）
# ---------------------------------------------------------------------------


def _constant_int(expr: Any) -> Optional[int]:
    expr_type = getattr(expr, "expr_type", None)
    if expr_type is None or expr_type != expr_type.__class__.CONSTANT:
        return None
    try:
        return int(getattr(expr, "value", 0) or 0)
    except (TypeError, ValueError, OverflowError):
        return None


def _expressions_equal(left: Any, right: Any) -> bool:
    equals = getattr(left, "equals", None)
    if not callable(equals):
        return False
    try:
        return bool(equals(right))
    except (AttributeError, LookupError, TypeError, ValueError, RecursionError):
        return False


def _signature_matches_expression(signature: Any, expr: Any) -> bool:
    if signature is None or expr is None:
        return False
    structural_key = getattr(expr, "structural_key", None)
    if not callable(structural_key):
        return False
    try:
        expr_signature = structural_key()
    except (AttributeError, LookupError, TypeError, ValueError, RecursionError):
        return False
    return normalize_signature_tuple(signature) == normalize_signature_tuple(
        expr_signature
    )


def normalize_signature_tuple(value: Any) -> Any:
    """list と tuple の違いを消して signature を比べられるようにする。"""

    if isinstance(value, (list, tuple)):
        return tuple(normalize_signature_tuple(item) for item in value)
    return value
