# -*- coding: utf-8 -*-
"""解析と再解析のヘルパー"""

from contextlib import nullcontext
from typing import Optional, Tuple
import time

from scripts.function_tracer_pcode.core import (
    FunctionReturnAnalysis,
    FunctionSignature,
    SignatureHypothesis,
)
from scripts.function_tracer_pcode.core.signature import (
    get_data_type_display_name,
    get_data_type_path,
    get_declared_type_signedness,
    get_declared_type_size_bits,
    get_declared_type_size_bytes,
    is_composite_data_type,
    is_floating_data_type,
    is_integral_data_type,
    is_pointer_data_type,
    is_undefined_data_type,
    is_unsigned_data_type,
    is_void_data_type,
)
from scripts.function_tracer_pcode.checker.phases.handler import (
    PhaseContext,
    PhaseResult,
    RetryAnalysisBase,
)
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
from scripts.function_tracer_pcode.checker.diagnostics import (
    ANALYSIS_SOURCE_FRESH,
    ANALYSIS_SOURCE_REUSE,
    REUSE_FALLBACK_BASE_SNAPSHOT_MUTATED,
    REUSE_FALLBACK_CONSTRUCTION_FAILED,
    REUSE_FALLBACK_FINGERPRINT_UNAVAILABLE,
    REUSE_FALLBACK_MODIFICATION_NUMBER_CHANGED,
    REUSE_FALLBACK_MODIFICATION_NUMBER_UNAVAILABLE,
    REUSE_FALLBACK_NO_SNAPSHOT,
    REUSE_FALLBACK_PROGRAM_IDENTITY_CHANGED,
    REUSE_FALLBACK_SHADOW_MISMATCH,
    AnalysisTimer,
    phase_timeline_of,
)
from scripts.function_tracer_pcode.checker.result_factory import (
    create_context_error_result,
    create_context_unknown_result,
    create_reanalysis_error,
)
from scripts.function_tracer_pcode.analysis.failure import (
    ANALYSIS_STATUS_DECOMPILATION_FAILED,
    ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
    ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
)


# Issue #107 (PR-B): 再利用ビューと fresh 再解析ビューが「後続 retry phase にとって同じ」と
# 言えるかを判定するための射影の版。``AnalysisSnapshot`` の一般的な意味は変えず、
# PR-107-B 専用の狭い射影としてここに置く。
REUSE_EQUIVALENCE_PROJECTION_VERSION = "retry-reuse-equivalence-v1"


def semantic_fingerprint_of(analysis) -> Optional[str]:
    """解析ビューの semantic fingerprint を返す（生成できなければ ``None``）。

    Issue #107 (PR-B): 既存の ``AnalysisSnapshot`` を使い、独自の指紋機構は作らない。
    ``snapshot_id`` は ``semantic_fingerprint`` の入力に含まれているので、この 1 つの
    文字列を比べれば取り違えも検出できる。opaque object を含むなどで正規化できない
    入力に対して ``SnapshotFingerprintCodec`` は例外を送出するので、その場合は ``None``
    を返し、呼び出し側は「再利用できない」として fresh へ倒す。**診断のための指紋生成が
    失敗しても判定を壊さない。**

    ただしこの指紋だけでは再利用の等価性判定に**足りない**。``to_dict()`` は
    ``parameters_without_runtime_objects()`` を通るため runtime の ``data_type_obj`` を
    落とすが、retry phase はその object から型名・サイズ・型分類・signedness を読む。
    等価性の判定には :func:`reuse_equivalence_key` を使うこと。
    """
    if analysis is None:
        return None
    try:
        from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot

        return str(AnalysisSnapshot.from_function_analysis(analysis).semantic_fingerprint)
    except Exception:
        return None


def runtime_type_projection(
    data_type_obj,
    fallback_name=None,
    fallback_size=None,
):
    """retry phase が runtime DataType から読む意味だけを安定値へ射影する。

    Java/PyGhidra object の identity は比較条件にしない。射影に含めるのは、
    ``checker/arch/mips64.py`` の P4-A 適用判定（``_get_param_type_string`` /
    ``_get_param_size``）と、``checker/phases/handler.py`` / ``semantics/typing/`` の
    型修正判定（``is_void_data_type`` / ``is_unsigned_data_type`` /
    ``is_suspicious_undefined_data_type`` / ``resolve_signed_counterpart_spec`` など）が
    実際に読む項目に対応する。``is_suspicious_undefined_data_type`` は
    「undefined か」＋サイズから決まり、``resolve_*_spec`` は型名・サイズ・signedness と
    program から決まるので、下の組で必要十分になる。
    """
    return (
        get_data_type_display_name(data_type_obj, fallback_name),
        get_data_type_path(data_type_obj),
        get_declared_type_size_bytes(data_type_obj, fallback_name, fallback_size=fallback_size),
        get_declared_type_size_bits(data_type_obj, fallback_name, fallback_size=fallback_size),
        get_declared_type_signedness(data_type_obj, fallback_name),
        is_void_data_type(data_type_obj, fallback_name),
        is_undefined_data_type(data_type_obj, fallback_name),
        is_composite_data_type(data_type_obj, fallback_name),
        is_pointer_data_type(data_type_obj, fallback_name),
        is_floating_data_type(data_type_obj, fallback_name),
        is_integral_data_type(data_type_obj, fallback_name),
        is_unsigned_data_type(data_type_obj, fallback_name),
    )


def _analysis_runtime_type_projection(analysis):
    """解析ビューの戻り値型と全 parameter について runtime 型意味を射影する。"""
    parameters = []
    for index, param in enumerate(getattr(analysis, "parameters", None) or ()):
        parameters.append(
            (
                int(param.get("index", index) or 0),
                runtime_type_projection(
                    param.get("data_type_obj"),
                    param.get("data_type"),
                    param.get("size"),
                ),
            )
        )
    return (
        runtime_type_projection(
            getattr(analysis, "return_type_obj", None),
            getattr(analysis, "return_type", None),
        ),
        tuple(parameters),
    )


def _completed_recovery_proof_projection(analysis):
    """完了済み recovery proof の同一性を安定値へ射影する。

    ``AnalysisSnapshot`` は proof state を意図的に除外する（derived proof 扱い）。
    ここでは一般の snapshot の意味は変えず、**再利用ビューが P0 時点の完了済み proof を
    そのまま持ち越していないか**を PR-107-B 側で検証するために射影する。
    """
    from scripts.function_tracer_pcode.proof.obligations.snapshot import (
        SnapshotFingerprintCodec,
    )

    return (
        SnapshotFingerprintCodec.digest(
            tuple(getattr(analysis, "completed_recovery_proof_ids", ()) or ())
        ),
        SnapshotFingerprintCodec.digest(
            tuple(getattr(analysis, "completed_recovery_proof_evidence", ()) or ())
        ),
    )


def reuse_equivalence_key(analysis) -> Optional[tuple]:
    """再利用ビューと fresh ビューが後続 phase にとって同じかを判定するキー。

    ``semantic_fingerprint``（意味的な解析内容）に加えて、
    **runtime 型の意味**（``semantic_fingerprint`` が落とす ``data_type_obj`` 由来の情報）と
    **完了済み recovery proof の同一性**（``AnalysisSnapshot`` が derived proof として
    除外する情報）を含める。どれか 1 つでも作れなければ ``None`` を返し、
    呼び出し側は再利用せず fresh へ倒す（fail-closed）。
    """
    if analysis is None:
        return None
    try:
        fingerprint = semantic_fingerprint_of(analysis)
        if fingerprint is None:
            return None
        return (
            REUSE_EQUIVALENCE_PROJECTION_VERSION,
            fingerprint,
            _analysis_runtime_type_projection(analysis),
            _completed_recovery_proof_projection(analysis),
        )
    except Exception:
        return None


def reuse_equivalence_digest(key) -> Optional[str]:
    """等価キーを診断へ載せるための短い文字列にする（比較そのものはキーで行う）。"""
    if key is None:
        return None
    try:
        from scripts.function_tracer_pcode.proof.obligations.snapshot import (
            SnapshotFingerprintCodec,
        )

        return str(SnapshotFingerprintCodec.digest(key))
    except Exception:
        return None


def reuse_equivalence_mismatch_kind(fresh_key, reuse_key) -> Optional[str]:
    """等価キーのどの成分が食い違ったかを診断用に返す。"""
    if fresh_key is None or reuse_key is None:
        return "key_unavailable"
    if fresh_key == reuse_key:
        return None
    if fresh_key[1] != reuse_key[1]:
        return "semantic_fingerprint"
    if fresh_key[2] != reuse_key[2]:
        return "runtime_type_semantics"
    if fresh_key[3] != reuse_key[3]:
        return "completed_recovery_proofs"
    return "unclassified"


def program_modification_number(program) -> Optional[int]:
    """Program の変更世代を返す（読めなければ ``None`` = 判定不能）。

    Ghidra の ``DomainObject.getModificationNumber()`` をそのまま読む。型修正自体は
    Program を書き換えないが、解析は ``DisassembleCommand`` で Program を書き換え得る
    （``analysis/returns/lifecycle.py``）ので、「型修正が Program を触らない」ことだけでは
    base snapshot の有効性を保証できない。意味的に無害な増加で fresh に倒れることは
    あっても、書き換えを見落とさない側を採る。
    """
    if program is None:
        return None
    getter = getattr(program, "getModificationNumber", None)
    if not callable(getter):
        return None
    try:
        value = getter()
    except Exception:
        return None
    if isinstance(value, bool):
        return None
    try:
        return int(value)
    except (TypeError, ValueError):
        return None


def build_retry_analysis_base(program, analysis) -> Optional[RetryAnalysisBase]:
    """raw 解析から再利用用の base state を作る。

    解析の複製・Program の世代・複製の等価キーの 3 つが揃わなければ ``None`` を返す
    （途中まで作った state を残さない）。複製は既存の ``semantic_successor()`` に任せ、
    新しい copy 規約を作らない。
    """
    if analysis is None:
        return None
    modification_number = program_modification_number(program)
    if modification_number is None:
        return None
    try:
        copied = analysis.semantic_successor()
    except Exception:
        return None
    equivalence_key = reuse_equivalence_key(copied)
    if equivalence_key is None:
        return None
    return RetryAnalysisBase(
        analysis=copied,
        program=program,
        modification_number=modification_number,
        equivalence_key=equivalence_key,
    )


def _store_retry_analysis_base(ctx: PhaseContext, side: str, base) -> None:
    """base state を PhaseContext へ入れる（3 要素は一体でしか入らない）。"""
    if base is None:
        return
    if side == "function1":
        ctx.retry_analysis_base1 = base
    else:
        ctx.retry_analysis_base2 = base


def _retry_analysis_base(ctx: PhaseContext, side: str) -> Optional[RetryAnalysisBase]:
    return ctx.retry_analysis_base1 if side == "function1" else ctx.retry_analysis_base2


def _seed_retry_analysis_base(ctx: PhaseContext, side: str, program, analysis) -> None:
    """P0 の raw 解析から base state を作る（作れなければ何も入れず、後で fresh に倒れる）。

    再利用が無効なら **何もしない**。複製・世代取得・等価キー生成のコストを、
    使わない run に払わせない（無効時は従来の処理と実質同じになる）。
    """
    if not _retry_reuse_enabled():
        return
    _store_retry_analysis_base(ctx, side, build_retry_analysis_base(program, analysis))


def _retry_reuse_enabled() -> bool:
    """再利用機構を動かすか。設定が読めなければ **無効**（fail-closed）。

    設定の欠落で未検証の再利用が暗黙に有効化されないよう、既定値は無効側に倒す。
    """
    try:
        from scripts.function_tracer_pcode.config import settings
    except Exception:
        return False
    return bool(getattr(settings, "RETRY_ANALYSIS_REUSE_ENABLED", False))


def _retry_reuse_shadow_enabled() -> bool:
    """fresh も構成して比較する validation mode か。設定が読めなければ **有効**。

    こちらは fresh を authoritative にする側なので、判断できないときは
    shadow（＝従来どおり fresh を採用する）へ倒すのが fail-closed になる。
    """
    try:
        from scripts.function_tracer_pcode.config import settings
    except Exception:
        return True
    return bool(getattr(settings, "RETRY_ANALYSIS_REUSE_SHADOW", True))


def _replay_signature_hypotheses(analysis, cached_analysis, program):
    """累積した型仮説を、記録された順序のまま重ねる。

    fresh 経路と再利用経路が同じ関数を使うことで、replay の順序が経路によって
    変わらないことを構成で保証する。
    """
    replayed = analysis
    for hypothesis_payload in list(getattr(cached_analysis, "signature_hypotheses", []) or []):
        hypothesis = SignatureHypothesis.from_dict(
            hypothesis_payload,
            program=program,
        )
        replayed = replayed.with_signature_hypothesis(hypothesis)
    return replayed


def analyze_and_check_with_analysis(
    checker,
    ctx: PhaseContext,
    retry_count: int = 0
) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
    """初回解析を実行し、その結果で stage plan を走らせる"""
    from scripts.function_tracer_pcode.analysis import ReturnAnalyzer

    start_time = time.time()
    timer = AnalysisTimer()
    checker._analysis_timer = timer
    phases = phase_timeline_of(checker)

    checker._debug_print(f"Analyzing function '{ctx.function_name1}' in {ctx.binary1_name}...")
    analyzer1 = ReturnAnalyzer(
        ctx.program1,
        debug=checker.debug,
        binary_id=ctx.binary1_id,
        enable_completed_recovery_proofs=getattr(checker, "enable_completed_recovery_proofs", True),
        external_call_effect_policy=getattr(checker, "external_call_effect_policy", None),
    )
    try:
        phases.record_reanalyzed_side("function1")
        with phases.measure("analysis", side="function1"):
            analysis1 = timer.timed(
                "function1",
                lambda: analyzer1.analyze_function_by_name(ctx.function_name1, ctx.decompile_timeout),
            )
        timer.record_analysis("function1", analysis1)
        timer.record_callee_parameter_cache("function1", analyzer1)
        timer.record_callee_analysis_cache("function1", analyzer1)
        timer.record_callee_unbound_reuse("function1", analyzer1)
        if analysis1 is None:
            failure = analyzer1.get_last_analysis_failure()
            failure_status = getattr(failure, "status", None)
            error_message = getattr(failure, "message", None) or analyzer1.get_last_function_lookup_error() or (
                f"Function '{ctx.function_name1}' not found in {ctx.binary1_name}"
            )
            if failure_status in {
                ANALYSIS_STATUS_DECOMPILATION_FAILED,
                ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
            }:
                return None, None, create_context_unknown_result(
                    ctx=ctx,
                    failure_status=failure_status,
                    message=error_message,
                    start_time=start_time,
                    retry_count=retry_count,
                )
            return None, None, create_context_error_result(
                ctx=ctx,
                error_message=error_message,
                start_time=start_time,
                retry_count=retry_count,
                failure_status=failure_status or ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
                failure_message=error_message,
            )
    finally:
        analyzer1.dispose()

    # Issue #107 (PR-B): retry phase が再利用する base は「仮説を重ねる前の raw 解析」。
    # ここが raw が存在する唯一の地点で、stage plan へ渡した後では派生・in-place 更新が
    # 入り得る。Program の世代は analyzer を dispose した後に読む。
    _seed_retry_analysis_base(ctx, "function1", ctx.program1, analysis1)

    checker._debug_print(f"Analyzing function '{ctx.function_name2}' in {ctx.binary2_name}...")
    analyzer2 = ReturnAnalyzer(
        ctx.program2,
        debug=checker.debug,
        binary_id=ctx.binary2_id,
        enable_completed_recovery_proofs=getattr(checker, "enable_completed_recovery_proofs", True),
        external_call_effect_policy=getattr(checker, "external_call_effect_policy", None),
    )
    try:
        phases.record_reanalyzed_side("function2")
        with phases.measure("analysis", side="function2"):
            analysis2 = timer.timed(
                "function2",
                lambda: analyzer2.analyze_function_by_name(ctx.function_name2, ctx.decompile_timeout),
            )
        timer.record_analysis("function2", analysis2)
        timer.record_callee_parameter_cache("function2", analyzer2)
        timer.record_callee_analysis_cache("function2", analyzer2)
        timer.record_callee_unbound_reuse("function2", analyzer2)
        if analysis2 is None:
            failure = analyzer2.get_last_analysis_failure()
            failure_status = getattr(failure, "status", None)
            error_message = getattr(failure, "message", None) or analyzer2.get_last_function_lookup_error() or (
                f"Function '{ctx.function_name2}' not found in {ctx.binary2_name}"
            )
            if failure_status in {
                ANALYSIS_STATUS_DECOMPILATION_FAILED,
                ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
            }:
                return analysis1, None, create_context_unknown_result(
                    ctx=ctx,
                    failure_status=failure_status,
                    message=error_message,
                    start_time=start_time,
                    retry_count=retry_count,
                    analysis1=analysis1,
                )
            return analysis1, None, create_context_error_result(
                ctx=ctx,
                error_message=error_message,
                start_time=start_time,
                retry_count=retry_count,
                analysis1=analysis1,
                failure_status=failure_status or ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
                failure_message=error_message,
            )
    finally:
        analyzer2.dispose()

    _seed_retry_analysis_base(ctx, "function2", ctx.program2, analysis2)

    if ctx.original_signature1 is None:
        ctx.original_signature1 = FunctionSignature.from_analysis(analysis1)
    if ctx.original_signature2 is None:
        ctx.original_signature2 = FunctionSignature.from_analysis(analysis2)

    checker._debug_print("Running stage plan...")
    with phases.measure("stage_plan"):
        result = checker._run_stage_plan(
            analysis1,
            analysis2,
            ctx.binary1_name,
            ctx.binary2_name,
            ctx.save_formula,
            type_fix_result=ctx.type_fix_result,
            retry_count=retry_count,
            original_signature1=ctx.original_signature1,
            original_signature2=ctx.original_signature2,
        )
    _attach_analysis_diagnostics(checker, result)

    return analysis1, analysis2, result


def selective_reanalysis_and_check(
    checker,
    ctx: PhaseContext,
    phase_result: PhaseResult,
    retry_count: int
) -> Tuple[Optional[FunctionReturnAnalysis], Optional[FunctionReturnAnalysis], EquivalenceResult]:
    """変更側だけ fresh analyze し、仮説を replay して stage plan を再実行する。"""

    from scripts.function_tracer_pcode.analysis import ReturnAnalyzer

    need_reanalyze1 = phase_result.changed_binary1
    need_reanalyze2 = phase_result.changed_binary2

    checker._debug_print(
        f"Selective analysis reuse: binary1_changed={need_reanalyze1}, "
        f"binary2_changed={need_reanalyze2}"
    )

    analysis1 = ctx.analysis1
    analysis2 = ctx.analysis2
    if analysis1 is None:
        return create_reanalysis_error(
            ctx,
            "Cached analysis for binary1 is not available",
            retry_count,
        )
    if analysis2 is None:
        return create_reanalysis_error(
            ctx,
            "Cached analysis for binary2 is not available",
            retry_count,
        )

    def _check_reuse_validity(
        side: str, program
    ) -> Tuple[Optional[RetryAnalysisBase], Optional[str]]:
        """再利用の事前条件を判定する（``(base, fallback_reason)`` を返す）。

        **fresh 解析より前に評価しなければならない。** fresh 解析自身が Program を
        書き換え得るので、後で評価すると常に「世代が変わった」になってしまう。
        """
        base = _retry_analysis_base(ctx, side)
        if base is None:
            return None, REUSE_FALLBACK_NO_SNAPSHOT
        if base.program is not program:
            return None, REUSE_FALLBACK_PROGRAM_IDENTITY_CHANGED
        current_modification = program_modification_number(program)
        if current_modification is None:
            return None, REUSE_FALLBACK_MODIFICATION_NUMBER_UNAVAILABLE
        if current_modification != base.modification_number:
            return None, REUSE_FALLBACK_MODIFICATION_NUMBER_CHANGED
        equivalence_key = reuse_equivalence_key(base.analysis)
        if equivalence_key is None:
            return None, REUSE_FALLBACK_FINGERPRINT_UNAVAILABLE
        if equivalence_key != base.equivalence_key:
            return None, REUSE_FALLBACK_BASE_SNAPSHOT_MUTATED
        return base, None

    def _build_reuse_candidate(
        *,
        base: RetryAnalysisBase,
        side: str,
        program,
        cached_analysis: FunctionReturnAnalysis,
        analyzer,
        phases,
        measure: bool,
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[str]]:
        """base の複製へ累積仮説を重ね、recurrence summary を張り直した候補を作る。

        構築の**後にも** base の指紋を確認する。``semantic_successor()`` が意図的に
        共有する field があり、recurrence refresh には入力の ``analysis_notes`` へ
        in-place 追記する経路もあるため、構築前の確認だけでは base 非汚染を保証できない。
        ``measure`` が偽のとき（shadow validation の比較用構築）は、fresh 側の内訳時間を
        汚さないよう phase の秒数へ加算しない。
        """
        try:
            candidate = base.analysis.semantic_successor()
            with phases.measure("hypothesis_replay") if measure else nullcontext():
                candidate = _replay_signature_hypotheses(candidate, cached_analysis, program)
            if getattr(candidate, "signature_hypotheses", None):
                with phases.measure("recurrence_refresh") if measure else nullcontext():
                    candidate = analyzer.refresh_structural_recurrence_summary(
                        candidate,
                        timeout=ctx.decompile_timeout,
                    )
        except Exception as exc:  # 構築できないなら fresh へ倒す
            checker._debug_print(f"Retry analysis reuse construction failed for {side}: {exc}")
            return None, REUSE_FALLBACK_CONSTRUCTION_FAILED
        post_key = reuse_equivalence_key(base.analysis)
        if post_key is None:
            return None, REUSE_FALLBACK_FINGERPRINT_UNAVAILABLE
        if post_key != base.equivalence_key:
            return None, REUSE_FALLBACK_BASE_SNAPSHOT_MUTATED
        return candidate, None

    def _reanalyze_with_hypotheses(
        *,
        program,
        function_name: str,
        binary_name: str,
        cached_analysis: FunctionReturnAnalysis,
    ) -> Tuple[Optional[FunctionReturnAnalysis], Optional[str], Optional[str]]:
        binary_id = ctx.binary1_id if program is ctx.program1 else ctx.binary2_id if program is ctx.program2 else None
        analyzer = ReturnAnalyzer(
            program,
            debug=checker.debug,
            binary_id=binary_id,
            enable_completed_recovery_proofs=getattr(checker, "enable_completed_recovery_proofs", True),
            external_call_effect_policy=getattr(checker, "external_call_effect_policy", None),
        )
        try:
            side = "function1" if program is ctx.program1 else "function2"
            timer = getattr(checker, "_analysis_timer", None) or AnalysisTimer()
            checker._analysis_timer = timer
            phases = phase_timeline_of(checker)
            phases.record_reanalyzed_side(side)

            # Issue #107 (PR-B): 事前条件は fresh 解析の前に見る（下の docstring 参照）。
            reuse_enabled = _retry_reuse_enabled()
            shadow_mode = _retry_reuse_shadow_enabled()
            base: Optional[RetryAnalysisBase] = None
            fallback_reason: Optional[str] = None
            if reuse_enabled:
                base, fallback_reason = _check_reuse_validity(side, program)

            if base is not None and not shadow_mode:
                # reuse mode: 事前条件を満たしていれば fresh 再解析を行わない。
                candidate, fallback_reason = _build_reuse_candidate(
                    base=base,
                    side=side,
                    program=program,
                    cached_analysis=cached_analysis,
                    analyzer=analyzer,
                    phases=phases,
                    measure=True,
                )
                phases.record_reuse_eligibility(side, candidate is not None)
                if candidate is not None:
                    checker._debug_print(
                        f"Retry analysis reuse accepted for {binary_name} ({side})"
                    )
                    phases.record_analysis_source(side, ANALYSIS_SOURCE_REUSE)
                    timer.record_analysis(side, candidate)
                    timer.record_callee_parameter_cache(side, analyzer)
                    timer.record_callee_analysis_cache(side, analyzer)
                    timer.record_callee_unbound_reuse(side, analyzer)
                    return candidate, None, None
                base = None  # 構築に失敗したので fresh へ倒す

            checker._debug_print(
                f"Fresh reanalysis requested for {binary_name} after signature-changing retry phase"
            )
            with phases.measure("analysis", side=side):
                fresh_analysis = timer.timed(
                    side,
                    lambda: analyzer.analyze_function_by_name(function_name, ctx.decompile_timeout),
                )
            timer.record_analysis(side, fresh_analysis)
            timer.record_callee_parameter_cache(side, analyzer)
            timer.record_callee_analysis_cache(side, analyzer)
            timer.record_callee_unbound_reuse(side, analyzer)
            if fresh_analysis is None:
                if reuse_enabled and base is None:
                    phases.record_reuse_eligibility(side, False)
                    phases.record_analysis_source(side, fallback_reason or ANALYSIS_SOURCE_FRESH)
                failure = analyzer.get_last_analysis_failure()
                failure_status = getattr(failure, "status", None)
                error_message = getattr(failure, "message", None) or analyzer.get_last_function_lookup_error() or (
                    f"Fresh reanalysis failed for '{function_name}' in {binary_name}"
                )
                return None, error_message, failure_status

            with phases.measure("hypothesis_replay"):
                replayed = _replay_signature_hypotheses(fresh_analysis, cached_analysis, program)
            if getattr(replayed, "signature_hypotheses", None):
                with phases.measure("recurrence_refresh"):
                    replayed = analyzer.refresh_structural_recurrence_summary(
                        replayed,
                        timeout=ctx.decompile_timeout,
                    )

            if not reuse_enabled:
                phases.record_analysis_source(side, ANALYSIS_SOURCE_FRESH)
                return replayed, None, None

            if base is not None:
                # shadow validation: 再利用側も構成して指紋を比べる。fresh が authoritative。
                candidate, construction_reason = _build_reuse_candidate(
                    base=base,
                    side=side,
                    program=program,
                    cached_analysis=cached_analysis,
                    analyzer=analyzer,
                    phases=phases,
                    measure=False,
                )
                phases.record_reuse_eligibility(side, candidate is not None)
                if candidate is None:
                    phases.record_analysis_source(side, construction_reason)
                    return replayed, None, None
                fresh_key = reuse_equivalence_key(replayed)
                reuse_key = reuse_equivalence_key(candidate)
                matched = (
                    fresh_key is not None
                    and reuse_key is not None
                    and fresh_key == reuse_key
                )
                mismatch_kind = reuse_equivalence_mismatch_kind(fresh_key, reuse_key)
                phases.record_shadow_comparison(
                    side,
                    fresh=reuse_equivalence_digest(fresh_key),
                    reuse=reuse_equivalence_digest(reuse_key),
                    matched=matched,
                    mismatch_kind=mismatch_kind,
                )
                if fresh_key is None or reuse_key is None:
                    phases.record_analysis_source(side, REUSE_FALLBACK_FINGERPRINT_UNAVAILABLE)
                elif matched:
                    phases.record_analysis_source(side, ANALYSIS_SOURCE_FRESH)
                else:
                    checker._debug_print(
                        f"Retry analysis reuse equivalence mismatch for {binary_name} "
                        f"({side}, {mismatch_kind})"
                    )
                    phases.record_analysis_source(side, REUSE_FALLBACK_SHADOW_MISMATCH)
                return replayed, None, None

            # 事前条件を満たさなかった。fresh が authoritative で、raw な fresh 解析から
            # base を張り直す（派生ビューは決して base にしない）。3 要素を作れないときは
            # 既存 base を据え置き、その side は以降も fresh のままにする。
            phases.record_reuse_eligibility(side, False)
            phases.record_analysis_source(side, fallback_reason or ANALYSIS_SOURCE_FRESH)
            _store_retry_analysis_base(
                ctx, side, build_retry_analysis_base(program, fresh_analysis)
            )
            return replayed, None, None
        finally:
            analyzer.dispose()

    if need_reanalyze1:
        analysis1, error_message, failure_status = _reanalyze_with_hypotheses(
            program=ctx.program1,
            function_name=ctx.function_name1,
            binary_name=ctx.binary1_name,
            cached_analysis=analysis1,
        )
        if analysis1 is None:
            checker._debug_print(f"Fresh reanalysis failed for binary1: {error_message}")
            if failure_status in {
                ANALYSIS_STATUS_DECOMPILATION_FAILED,
                ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
            }:
                return ctx.analysis1, ctx.analysis2, create_context_unknown_result(
                    ctx=ctx,
                    failure_status=failure_status,
                    message=str(error_message),
                    start_time=time.time(),
                    retry_count=retry_count,
                    analysis1=ctx.analysis1,
                    analysis2=ctx.analysis2,
                )
            return create_reanalysis_error(
                ctx,
                str(error_message),
                retry_count,
                failure_status=failure_status,
            )

    if need_reanalyze2:
        analysis2, error_message, failure_status = _reanalyze_with_hypotheses(
            program=ctx.program2,
            function_name=ctx.function_name2,
            binary_name=ctx.binary2_name,
            cached_analysis=analysis2,
        )
        if analysis2 is None:
            checker._debug_print(f"Fresh reanalysis failed for binary2: {error_message}")
            if failure_status in {
                ANALYSIS_STATUS_DECOMPILATION_FAILED,
                ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
            }:
                return ctx.analysis1, ctx.analysis2, create_context_unknown_result(
                    ctx=ctx,
                    failure_status=failure_status,
                    message=str(error_message),
                    start_time=time.time(),
                    retry_count=retry_count,
                    analysis1=ctx.analysis1,
                    analysis2=ctx.analysis2,
                )
            return create_reanalysis_error(
                ctx,
                str(error_message),
                retry_count,
                failure_status=failure_status,
            )

    ctx.analysis1 = analysis1
    ctx.analysis2 = analysis2

    with phase_timeline_of(checker).measure("stage_plan"):
        result = checker._run_stage_plan(
            analysis1,
            analysis2,
            ctx.binary1_name,
            ctx.binary2_name,
            ctx.save_formula,
            type_fix_result=ctx.type_fix_result,
            retry_count=retry_count,
            original_signature1=ctx.original_signature1,
            original_signature2=ctx.original_signature2,
        )
    _attach_analysis_diagnostics(checker, result)

    return analysis1, analysis2, result


def _attach_analysis_diagnostics(checker, result) -> None:
    """解析時間と式サイズを結果に添付する（非署名の診断領域）。"""
    timer = getattr(checker, "_analysis_timer", None)
    if timer is None or result is None:
        return
    try:
        result.diagnostics = timer.snapshot()
    except Exception:  # diagnostics never fail the verdict
        return
