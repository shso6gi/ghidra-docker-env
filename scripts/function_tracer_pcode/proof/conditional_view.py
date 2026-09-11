# -*- coding: utf-8 -*-
"""Conditional (assumption-dependent) semantic view over external catalog calls.

Issue #20 PR-20-B2。B1 の decision-neutral な ``CallModelCandidateRef`` と
PR-20-A の proof-owned ``AssumptionPremise`` から、

    candidate → canonical ``Expression(CALL, ...)`` → UF 宣言
              → assumption 付き conditional semantic view

を構成する **dormant な基盤**を提供する。receipt の発行、production conditional
lane の起動、conditional verdict は PR-20-B3 の責務であり、本 module は
production からは呼ばれない。

責務の分離（正本 v4 §4.3.2 / §4.3.3）:

* ``analysis`` 層は仮定を持たない。external の空 body を no-write evidence に
  しないし、``effect_summary`` も ``DeferredCallInfo.effect_class`` も変えない。
* 「この external callee は catalog の仕様どおりに振る舞う（同じ値意味、
  observable memory write 無し、normal return）」という契約は、本 module が
  作る ``AssumptionPremise`` が明示的に負う。
* view は base analysis を **変更しない**。``semantic_successor()`` で別実体を
  作り、共有される ``effect_summary`` には一切書き込まない。

soundness の要点:

* 未検証の ``DeferredCallInfo.arguments`` を proof evidence に昇格しない。
  PR-20-D の argument recovery が ``complete`` と言った callsite だけを写像し、
  catalog signature と幅が完全一致する場合に限る。足りない・食い違うなら
  その callsite は写像せず、元の UNKNOWN のまま残す（fail closed）。
* 引数式はそのまま operand になるので、``log(x)`` と ``log(x+1)`` は別の CALL
  として保たれる。fresh argument は side-specific のままで、ABI slot が一致
  するだけで左右の値を couple することはない。
* candidate があること自体は callsite correspondence の根拠にしない。本 module
  は片側の analysis だけを見て view を作る。
* ``observe_errno`` / ``observe_fenv`` が有効なら view を作らない（B1 の
  candidate gate と同じ境界）。

assumption_set は **最小化しない**（正本 §4.3.6）。UF が simplification で
消えても、effect term が最終 formula に現れなくても、premise は落とさない。
B3 は ``view.assumption_set`` をそのまま
``ConditionalDecisiveProofReceipt.assumption_dependencies`` に使える。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.analysis.effects.pure_function_catalog import (
    catalog_signature_widths,
)
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.render_smt import (
    CallDeclarationConflict,
    collect_call_smt_declarations,
    expression_smt_bit_width,
    normalize_call_symbol_name,
)
from scripts.function_tracer_pcode.core.runtime_refs import CallModelCandidateRef
from scripts.function_tracer_pcode.proof.assumptions import (
    AssumptionKind,
    AssumptionPremise,
    normalize_assumption_premises,
)
# 同一 package 内の deferred-call UNKNOWN 走査。ここで書き直すと「どの式が
# どの deferred call を参照しているか」の判定が二重実装になるので再利用する。
from scripts.function_tracer_pcode.proof.deferred_call_abstraction import (
    _deferred_unknown_sizes,
)


CONDITIONAL_VIEW_BUILDER_VERSION = "conditional-external-call-view-v1"

#: PR-20-D の argument recovery がこの status を出した callsite だけを写像する。
PROVEN_ARGUMENT_RECOVERY_STATUS = "complete"

# --- view 全体を作れなかった理由 -------------------------------------------
VIEW_REFUSED_OBSERVATION_ACTIVE = "conditional_view_observation_active"
VIEW_REFUSED_OBSERVATION_POLICY_UNAVAILABLE = "conditional_view_observation_policy_unavailable"
VIEW_REFUSED_ANALYSIS_UNAVAILABLE = "conditional_view_analysis_unavailable"
VIEW_REFUSED_NO_MAPPED_CALL = "conditional_view_no_mapped_call"
VIEW_REFUSED_DECLARATION_CONFLICT = "conditional_view_call_declaration_conflict"

# --- callsite ごとに写像しなかった理由 -------------------------------------
CALL_SKIPPED_NO_CANDIDATE = "call_model_candidate_absent"
CALL_SKIPPED_SIGNATURE_UNUSABLE = "call_catalog_signature_unusable"
CALL_SKIPPED_ARGUMENT_EVIDENCE_UNPROVEN = "call_argument_evidence_unproven"
CALL_SKIPPED_ARGUMENT_ARITY_MISMATCH = "call_argument_arity_mismatch"
CALL_SKIPPED_ARGUMENT_WIDTH_MISMATCH = "call_argument_width_mismatch"
CALL_SKIPPED_RETURN_WIDTH_MISMATCH = "call_return_width_mismatch"
CALL_SKIPPED_NOT_REFERENCED = "call_not_referenced_by_returns"


# --- assumption -----------------------------------------------------------


def external_callee_spec_premise(
    candidate: CallModelCandidateRef,
    *,
    argument_widths: Sequence[int],
    return_width_bits: int,
) -> AssumptionPremise:
    """candidate から ``EXTERNAL_CALLEE_SPEC`` premise を作る。

    premise の意味は「この provenance で観測された external symbol は、この
    catalog provider の canonical symbol の仕様どおりに振る舞う」であり、
    値意味・observable memory write 無し・normal return の 3 つを明示的に
    含む。external であることそれ自体は根拠ではなく、その上に置く仮定である。
    """

    if type(candidate) is not CallModelCandidateRef:
        raise TypeError("external callee spec premise requires a CallModelCandidateRef")
    return AssumptionPremise(
        kind=AssumptionKind.EXTERNAL_CALLEE_SPEC,
        subject=candidate.canonical_symbol,
        payload=(
            ("behaves_as_catalog_specification", True),
            ("canonical_symbol", candidate.canonical_symbol),
            ("catalog_provider", candidate.provider),
            ("candidate_key", candidate.candidate_key),
            ("signature_key", candidate.signature_key),
            ("argument_width_bits", tuple(int(width) for width in argument_widths)),
            ("return_width_bits", int(return_width_bits)),
            ("provenance_key", candidate.provenance_key),
            ("no_observable_memory_write", True),
            ("returns_normally", True),
            ("observation_contract", (("observe_errno", False), ("observe_fenv", False))),
        ),
    )


# --- view -----------------------------------------------------------------


@dataclass(frozen=True)
class ConditionalCallModel:
    """1 個の callsite を canonical CALL/UF として扱う、仮定付きの写像。"""

    deferred_call_key: Tuple[Any, ...]
    canonical_symbol: str
    uf_symbol: str
    argument_widths: Tuple[int, ...]
    return_width_bits: int
    candidate_key: Tuple[Any, ...]
    premise: AssumptionPremise

    def uf_identity(self) -> Tuple[Any, ...]:
        """左右で同一になるべき UF の identity。

        canonical symbol と **catalog の厳密な引数幅・戻り幅**だけで決まる。
        callsite 位置・provenance・引数式は入らない（同じ関数の別呼び出しは
        同じ UF、別関数は別 UF）。
        """

        return (self.uf_symbol, self.argument_widths, self.return_width_bits)


@dataclass(frozen=True)
class ConditionalSemanticView:
    """assumption 付きの解析 view。base analysis とは別実体。"""

    binary_id: Optional[str]
    view_builder_version: str
    call_models: Tuple[ConditionalCallModel, ...]
    assumption_set: Tuple[AssumptionPremise, ...]
    call_declarations: Tuple[Tuple[str, Tuple[int, ...], int], ...]
    unmapped_calls: Tuple[Tuple[Tuple[Any, ...], str], ...] = ()
    analysis: Any = field(default=None, compare=False, hash=False, repr=False)

    def __post_init__(self) -> None:
        if not self.call_models:
            raise ValueError("a conditional view maps at least one call")
        if not self.assumption_set:
            raise ValueError("a conditional view carries a non-empty assumption set")

    def view_key(self) -> Tuple[Any, ...]:
        return (
            self.view_builder_version,
            self.binary_id,
            tuple(model.uf_identity() for model in self.call_models),
            tuple(premise.premise_key() for premise in self.assumption_set),
        )

    def call_declaration_map(self) -> Dict[str, Tuple[Tuple[int, ...], int]]:
        return {name: (widths, bits) for name, widths, bits in self.call_declarations}


@dataclass(frozen=True)
class ConditionalViewResult:
    """view を作れたか、作れなかったならその理由。"""

    view: Optional[ConditionalSemanticView] = None
    refusal_reason: Optional[str] = None
    call_diagnostics: Tuple[Tuple[Tuple[Any, ...], str], ...] = ()

    def __post_init__(self) -> None:
        if (self.view is None) == (self.refusal_reason is None):
            raise ValueError(
                "a conditional view result carries exactly one of view / refusal_reason"
            )

    @property
    def constructed(self) -> bool:
        return self.view is not None


def _refused(
    reason: str,
    diagnostics: Sequence[Tuple[Tuple[Any, ...], str]] = (),
) -> ConditionalViewResult:
    return ConditionalViewResult(
        view=None,
        refusal_reason=reason,
        call_diagnostics=tuple(diagnostics),
    )


def _observation_refusal(policy: Any) -> Optional[str]:
    observe_errno = getattr(policy, "observe_errno", None)
    observe_fenv = getattr(policy, "observe_fenv", None)
    if type(observe_errno) is not bool or type(observe_fenv) is not bool:
        return VIEW_REFUSED_OBSERVATION_POLICY_UNAVAILABLE
    if observe_errno or observe_fenv:
        return VIEW_REFUSED_OBSERVATION_ACTIVE
    return None


def _deferred_call_key(info: Any) -> Optional[Tuple[Any, ...]]:
    deferred_call_ref = getattr(info, "deferred_call_ref", None)
    stable_key = getattr(deferred_call_ref, "stable_key", None)
    if not callable(stable_key):
        return None
    return stable_key()


def _observed_unknown_sizes(analysis: Any) -> Dict[Tuple[Any, ...], set]:
    """returns / guards が参照する deferred-call UNKNOWN のサイズ集合。"""

    observed: Dict[Tuple[Any, ...], set] = {}
    for ret in getattr(analysis, "returns", None) or []:
        for key, sizes in _deferred_unknown_sizes(getattr(ret, "value", None)).items():
            observed.setdefault(key, set()).update(sizes)
        for condition in getattr(ret, "conditions", None) or []:
            expression = getattr(condition, "expression", None)
            for key, sizes in _deferred_unknown_sizes(expression).items():
                observed.setdefault(key, set()).update(sizes)
    return observed


def _call_model_for(
    info: Any,
    deferred_key: Tuple[Any, ...],
    observed_sizes: Mapping[Tuple[Any, ...], set],
) -> Tuple[Optional[ConditionalCallModel], Optional[str]]:
    candidate = getattr(info, "call_model_candidate", None)
    if type(candidate) is not CallModelCandidateRef:
        return None, CALL_SKIPPED_NO_CANDIDATE

    signature = catalog_signature_widths(candidate.signature_key)
    if signature is None:
        return None, CALL_SKIPPED_SIGNATURE_UNUSABLE
    argument_widths, return_width_bits = signature

    # PR-20-D が「復元しきった」と言った callsite だけを写像する。partial /
    # inconclusive を proof evidence に昇格しない。
    if getattr(info, "call_argument_recovery_status", None) != PROVEN_ARGUMENT_RECOVERY_STATUS:
        return None, CALL_SKIPPED_ARGUMENT_EVIDENCE_UNPROVEN

    arguments = list(getattr(info, "arguments", None) or [])
    if len(arguments) != len(argument_widths):
        return None, CALL_SKIPPED_ARGUMENT_ARITY_MISMATCH
    for argument, width in zip(arguments, argument_widths):
        if argument is None:
            return None, CALL_SKIPPED_ARGUMENT_WIDTH_MISMATCH
        observed_width = int(expression_smt_bit_width(argument) or 0)
        if observed_width != int(width):
            return None, CALL_SKIPPED_ARGUMENT_WIDTH_MISMATCH

    sizes = observed_sizes.get(deferred_key)
    if not sizes:
        return None, CALL_SKIPPED_NOT_REFERENCED
    # 参照側が幅を持っていない (size 0) のは「観測できていない」であって
    # 「食い違っている」ではない。その場合の戻り幅は callee の宣言 signature が
    # authority なので catalog の幅を使う（既存の pure-return 経路が
    # ``expr.size or summary_size`` としているのと同じ扱い）。実際に別の幅で
    # 観測されているなら、それは食い違いなので fail closed。
    observed_widths = {int(size or 0) * 8 for size in sizes if int(size or 0) > 0}
    if any(width != int(return_width_bits) for width in observed_widths):
        return None, CALL_SKIPPED_RETURN_WIDTH_MISMATCH

    premise = external_callee_spec_premise(
        candidate,
        argument_widths=argument_widths,
        return_width_bits=return_width_bits,
    )
    return (
        ConditionalCallModel(
            deferred_call_key=deferred_key,
            canonical_symbol=candidate.canonical_symbol,
            uf_symbol=normalize_call_symbol_name(candidate.canonical_symbol),
            argument_widths=tuple(int(width) for width in argument_widths),
            return_width_bits=int(return_width_bits),
            candidate_key=candidate.candidate_key,
            premise=premise,
        ),
        None,
    )


def _canonical_call_expression(
    model: ConditionalCallModel,
    info: Any,
) -> Expression:
    """candidate の canonical symbol と、実際の引数式から CALL を作る。

    operand は callsite ごとの引数式そのものなので、``log(x)`` と ``log(x+1)``
    は別の CALL のまま保たれる。
    """

    return Expression(
        expr_type=ExpressionType.CALL,
        name=model.canonical_symbol,
        operands=list(getattr(info, "arguments", None) or []),
        size=model.return_width_bits // 8,
    )


def _rewrite_expression(
    expr: Optional[Expression],
    replacements: Mapping[Tuple[Any, ...], Expression],
) -> Optional[Expression]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        deferred_call_ref = getattr(runtime_ref, "deferred_call_ref", None)
        stable_key = getattr(deferred_call_ref, "stable_key", None)
        deferred_key = stable_key() if callable(stable_key) else None
        replacement = replacements.get(deferred_key) if deferred_key is not None else None
        if replacement is not None:
            return replacement

    if expr.expr_type == ExpressionType.PHI and expr.value:
        rebuilt_branches = []
        for condition, value in expr.value:
            rebuilt_condition = (
                Condition(
                    _rewrite_expression(condition.expression, replacements),
                    condition.negated,
                )
                if condition is not None
                else None
            )
            rebuilt_branches.append(
                (rebuilt_condition, _rewrite_expression(value, replacements))
            )
        rebuilt = Expression.phi(rebuilt_branches)
        rebuilt.size = expr.size
        return rebuilt

    if not expr.operands:
        return expr

    return Expression(
        expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=[_rewrite_expression(operand, replacements) for operand in expr.operands],
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=getattr(expr, "read_order_key", None),
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
    )


def _rewrite_analysis(
    analysis: FunctionReturnAnalysis,
    replacements: Mapping[Tuple[Any, ...], Expression],
) -> FunctionReturnAnalysis:
    """base を変えずに、CALL へ写像した別実体を返す。

    ``semantic_successor()`` の copy policy に従う。共有される
    ``effect_summary`` には書き込まない（assumed no-write を analysis fact に
    昇格させないため）。
    """

    view_analysis = analysis.semantic_successor(
        parameters=[dict(param) for param in (analysis.parameters or [])],
        returns=[],
    )
    view_analysis.returns = [
        ReturnInfo(
            address=ret.address,
            value=_rewrite_expression(ret.value, replacements),
            conditions=[
                Condition(
                    _rewrite_expression(condition.expression, replacements),
                    condition.negated,
                )
                for condition in ret.conditions
            ],
            branch_index=ret.branch_index,
            pcode_identity=ret.pcode_identity,
            pcode_order=ret.pcode_order,
            pcode_time=ret.pcode_time,
            pcode_op_ref=getattr(ret, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(ret, "return_value_pcode_op_refs", ()) or ()
            ),
        )
        for ret in (analysis.returns or [])
    ]
    # 写像した callsite は premise が値意味と no-write を引き受けたので、この
    # view では deferred call として残さない。base の deferred_calls は不変。
    view_analysis.deferred_calls = {
        key: info
        for key, info in (view_analysis.deferred_calls or {}).items()
        if key not in replacements
    }
    note = "conditional_external_call_view"
    if note not in view_analysis.analysis_notes:
        view_analysis.analysis_notes.append(note)
    return view_analysis


def create_conditional_view(
    analysis: Any,
    *,
    observation_policy: Any,
) -> ConditionalViewResult:
    """base analysis から conditional semantic view を構成する。

    ``ObligationRuntimeSession`` 等の production 経路からは呼ばれない
    （PR-20-B3 が lane を接続するまで dormant）。base analysis は変更しない。
    """

    refusal = _observation_refusal(observation_policy)
    if refusal is not None:
        return _refused(refusal)
    if analysis is None or not hasattr(analysis, "semantic_successor"):
        return _refused(VIEW_REFUSED_ANALYSIS_UNAVAILABLE)

    observed_sizes = _observed_unknown_sizes(analysis)
    replacements: Dict[Tuple[Any, ...], Expression] = {}
    models: List[ConditionalCallModel] = []
    diagnostics: List[Tuple[Tuple[Any, ...], str]] = []

    deferred_calls = getattr(analysis, "deferred_calls", None) or {}
    for map_key in sorted(deferred_calls, key=repr):
        info = deferred_calls[map_key]
        deferred_key = _deferred_call_key(info)
        if deferred_key is None:
            continue
        model, reason = _call_model_for(info, deferred_key, observed_sizes)
        if model is None:
            diagnostics.append((deferred_key, reason or CALL_SKIPPED_NO_CANDIDATE))
            continue
        replacements[deferred_key] = _canonical_call_expression(model, info)
        models.append(model)

    if not models:
        return _refused(VIEW_REFUSED_NO_MAPPED_CALL, diagnostics)

    view_analysis = _rewrite_analysis(analysis, replacements)

    declarations: Dict[str, Tuple[Tuple[int, ...], int]] = {}
    try:
        for ret in view_analysis.returns or []:
            if collect_call_smt_declarations(ret.value, declarations) is None:
                return _refused(VIEW_REFUSED_DECLARATION_CONFLICT, diagnostics)
            for condition in ret.conditions or []:
                if (
                    collect_call_smt_declarations(
                        getattr(condition, "expression", None), declarations
                    )
                    is None
                ):
                    return _refused(VIEW_REFUSED_DECLARATION_CONFLICT, diagnostics)
    except CallDeclarationConflict:
        # 同じ canonical symbol に別 sort が要求された。silent rename も
        # 片側優先もせず view ごと fail closed にする。
        return _refused(VIEW_REFUSED_DECLARATION_CONFLICT, diagnostics)

    # assumption は最小化しない。deterministic な順序で dedup するだけ。
    assumption_set = normalize_assumption_premises(
        sorted((model.premise for model in models), key=lambda premise: premise.premise_key())
    )

    view = ConditionalSemanticView(
        binary_id=getattr(analysis, "binary_id", None),
        view_builder_version=CONDITIONAL_VIEW_BUILDER_VERSION,
        call_models=tuple(models),
        assumption_set=assumption_set,
        call_declarations=tuple(
            (name, widths, bits) for name, (widths, bits) in sorted(declarations.items())
        ),
        unmapped_calls=tuple(diagnostics),
        analysis=view_analysis,
    )
    return ConditionalViewResult(view=view, call_diagnostics=tuple(diagnostics))


# --- conditional formula entry point --------------------------------------


@dataclass(frozen=True)
class ConditionalEquivalenceFormula:
    """conditional view 2 つから組んだ formula と、それが依存する仮定。

    formula と assumption set を必ず一緒に運ぶための最小 adapter。receipt でも
    verdict でもない（それらは PR-20-B3）。``assumption_set`` は両 view の和で、
    **最小化しない**ので B3 がそのまま ``assumption_dependencies`` に使える。
    """

    formula: str
    assumption_set: Tuple[AssumptionPremise, ...]
    builder_result: Any = field(default=None, compare=False, hash=False, repr=False)

    def __post_init__(self) -> None:
        if not self.assumption_set:
            raise ValueError("a conditional formula carries a non-empty assumption set")


def build_conditional_equivalence_formula(
    left_view: ConditionalSemanticView,
    right_view: ConditionalSemanticView,
    *,
    debug: bool = False,
) -> ConditionalEquivalenceFormula:
    """conditional view 由来の formula を組む **唯一の入口**。

    ``FormulaBuilder(allow_call=True)`` を production 側で直接使わせないための薄い
    adapter。``view.analysis`` 以外を conditional builder へ渡す経路を作らない。
    lane の起動・receipt 発行・verdict は PR-20-B3 の責務で、ここにはない。

    **builder option を外から注入させない。** ``assume_fp_non_nan`` のように
    formula へ追加の前提を入れる option を通すと、formula が依存する仮定と
    :attr:`ConditionalEquivalenceFormula.assumption_set` が食い違い、B3 が receipt へ
    繋いだときに assumption dependency が欠落する。したがって semantics を変え得る
    option は受け取らず、``debug``（出力に影響しない診断印字）だけを許す。
    FP non-NaN を仮定として正式に扱うなら、対応する premise を先に定義する必要が
    あり、それは本 PR の scope ではない。
    """

    from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder

    for view in (left_view, right_view):
        if type(view) is not ConditionalSemanticView:
            raise TypeError(
                "conditional formulas are built from ConditionalSemanticView only"
            )
    if type(debug) is not bool:
        raise TypeError("debug must be an exact bool")
    # semantics を決める option は既定任せにせず**すべて明示**する。FormulaBuilder
    # の既定が将来変わっても conditional formula の意味が黙って動かないようにする
    # ため（`assume_fp_non_nan` が既定で真になれば、記録されない前提が formula に
    # 入る）。新しい option を公開しないので、値はここが唯一の決定点。
    builder = FormulaBuilder(
        debug=debug,
        exclude_ub=True,
        assume_fp_non_nan=False,
        allow_call=True,
    )
    if builder.assume_fp_non_nan:
        raise ValueError(
            "a conditional formula must not carry untracked input-domain assumptions"
        )
    result = builder.build_equivalence_formula_extended(
        left_view.analysis,
        right_view.analysis,
    )
    # dependency minimization はしない。両 view の assumption をそのまま合わせる。
    assumption_set = normalize_assumption_premises(
        sorted(
            (*left_view.assumption_set, *right_view.assumption_set),
            key=lambda premise: premise.premise_key(),
        )
    )
    return ConditionalEquivalenceFormula(
        formula=result.formula,
        assumption_set=assumption_set,
        builder_result=result,
    )
