# -*- coding: utf-8 -*-
"""Phase workflow orchestration for EquivalenceChecker."""

import time

from scripts.function_tracer_pcode.checker.debug_trace import DebugTrace, TransitionReason
from scripts.function_tracer_pcode.checker.diagnostics import (
    PhaseTimeline,
    attach_phase_timings,
    phase_timeline_of,
    unknown_reason_ids,
)
from scripts.function_tracer_pcode.checker.phases.handler import (
    DEFAULT_PHASE_PLAN,
    PhaseContext,
    PhaseID,
    PhaseResult,
    PhaseSpec,
)
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult


# `checker` が `_phase_timeline` を持っていなかったことを表す番兵。
_NO_PHASE_TIMELINE = object()


def run_check_from_binaries(
    checker,
    program1,
    program2,
    function_name1: str,
    function_name2: str,
    decompile_timeout: int = 60,
    save_formula: bool = False,
    retry_with_type_fix: bool = False,
    binary1_id: str | None = None,
    binary2_id: str | None = None,
):
    """`check_from_binaries()` の phase workflow を実行する

    phase ごとの内訳時間（Issue #107）は判定に関与しない診断なので、どの経路で
    抜けても最後に 1 箇所だけで結果へ添付する。
    """
    phase_timeline = PhaseTimeline()
    previous_timeline = getattr(checker, "_phase_timeline", _NO_PHASE_TIMELINE)
    checker._phase_timeline = phase_timeline
    result = None
    try:
        result = _run_phase_plan(
            checker,
            program1,
            program2,
            function_name1,
            function_name2,
            decompile_timeout=decompile_timeout,
            save_formula=save_formula,
            retry_with_type_fix=retry_with_type_fix,
            binary1_id=binary1_id,
            binary2_id=binary2_id,
        )
        return result
    finally:
        try:
            attach_phase_timings(result, phase_timeline)
        finally:
            # この run の timeline を checker に残さない。残すと、workflow を経由しない
            # 後続処理の `phase_timeline_of(checker)` が前 run の記録先を掴んでしまう。
            if previous_timeline is _NO_PHASE_TIMELINE:
                try:
                    del checker._phase_timeline
                except AttributeError:
                    pass
            else:
                checker._phase_timeline = previous_timeline


def _run_phase_plan(
    checker,
    program1,
    program2,
    function_name1: str,
    function_name2: str,
    decompile_timeout: int = 60,
    save_formula: bool = False,
    retry_with_type_fix: bool = False,
    binary1_id: str | None = None,
    binary2_id: str | None = None,
):
    """phase plan 本体（診断の添付は呼び出し側が行う）"""
    start_time = time.time()
    phase_timeline = phase_timeline_of(checker)
    binary1_name = program1.getName() if hasattr(program1, "getName") else "binary1"
    binary2_name = program2.getName() if hasattr(program2, "getName") else "binary2"

    type_fix_result = TypeFixResult()
    primary_phases = [phase_spec.phase_id.value for phase_spec in DEFAULT_PHASE_PLAN]
    debug_trace = DebugTrace(
        planned_phases=primary_phases,
        known_phases=primary_phases + [
            PhaseID.P4A_MIPS64_ABI.value,
            "P4B_MIPS64_SPURIOUS",
            "P4C_RETURN_TYPE_FIX",
        ],
    )
    ctx = PhaseContext(
        program1=program1,
        program2=program2,
        function_name1=function_name1,
        function_name2=function_name2,
        binary1_name=binary1_name,
        binary2_name=binary2_name,
        binary1_id=binary1_id,
        binary2_id=binary2_id,
        decompile_timeout=decompile_timeout,
        save_formula=save_formula,
        type_fix_result=type_fix_result,
        original_signature1=None,
        original_signature2=None,
    )

    type_fixer1 = None
    type_fixer2 = None
    if retry_with_type_fix:
        type_fixer1 = checker._create_type_fixer(program1)
        type_fixer2 = checker._create_type_fixer(program2)

    result = None
    retry_count = 0
    first_phase = True
    attempt_id = 0

    for phase_spec in DEFAULT_PHASE_PLAN.copy():
        phase_id = phase_spec.phase_id

        checker._debug_print("=" * 60)
        checker._debug_print(f"Phase {phase_id.value}: {phase_spec.description}")
        checker._debug_print("=" * 60)

        if first_phase:
            first_phase = False
            type_fix_result.retry_phase = "initial"

            phase_timeline.begin(
                phase_id.value,
                retry_name="initial",
                attempt_id=attempt_id,
                reason_before=unknown_reason_ids(result),
            )
            analysis1, analysis2, result = checker._analyze_and_check_with_analysis(
                ctx, retry_count=retry_count
            )
            phase_record = phase_timeline.end(reason_after=unknown_reason_ids(result))
            ctx.analysis1 = analysis1
            ctx.analysis2 = analysis2
            ctx.original_signature1 = result.function1_signature
            ctx.original_signature2 = result.function2_signature
        else:
            if not retry_with_type_fix:
                checker._debug_print("Stopping: retry_with_type_fix=False")
                break

            if type_fixer1 is None or type_fixer2 is None:
                checker._debug_print("Stopping: type_fixer not available")
                break

            phase_timeline.begin(
                phase_id.value,
                attempt_id=attempt_id,
                reason_before=unknown_reason_ids(result),
            )
            with phase_timeline.measure("phase_fix"):
                phase_result = checker.phase_handler.execute_phase(
                    phase_spec,
                    ctx,
                    type_fixer1,
                    type_fixer2,
                    checker._get_params_via_decompile,
                )
            phase_timeline.record_phase_result(phase_result)

            if not phase_result.applied:
                phase_record = phase_timeline.end(reason_after=unknown_reason_ids(result))
                checker._debug_print(
                    f"Phase {phase_id.value}: No changes applied, skipping recheck"
                )
                checker._record_attempt(
                    debug_trace,
                    attempt_id,
                    retry_count,
                    phase_id.value,
                    [],
                    checker.strategy_name,
                    None,
                    TransitionReason.NO_CHANGES.value,
                    type_fix_result,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    0.0,
                    phase_diagnostics=phase_record,
                )
                attempt_id += 1
                continue

            retry_count += 1
            type_fix_result.retry_phase = phase_result.retry_name

            analysis1, analysis2, result = checker._selective_reanalysis_and_check(
                ctx, phase_result, retry_count=retry_count
            )
            phase_record = phase_timeline.end(reason_after=unknown_reason_ids(result))
            ctx.analysis1 = analysis1
            ctx.analysis2 = analysis2

        will_try_phase4b = False
        if result.is_equivalent is False and retry_with_type_fix:
            abi_constraints_check = checker.phase_handler.run_phase4_mips64_retry(result, ctx)
            will_try_phase4b = abi_constraints_check is not None

        transition_reason = checker._get_transition_reason(
            result, retry_with_type_fix, phase_id.value, will_try_phase4b
        )
        checker._record_attempt_from_result(
            debug_trace,
            attempt_id,
            retry_count,
            phase_id.value,
            result,
            transition_reason,
            type_fix_result,
            phase_diagnostics=phase_record,
        )
        attempt_id += 1

        finalized = _finalize_if_terminal(
            checker, result, debug_trace, start_time, phase_id.value
        )
        if finalized is not None:
            return finalized

        if result.is_equivalent is False:
            checker._debug_print(f"Phase {phase_id.value}: SAT - checking for Phase 4-B eligibility")
            attempted_return_type_fix = False

            if retry_with_type_fix and will_try_phase4b:
                abi_constraints = checker.phase_handler.run_phase4_mips64_retry(result, ctx)
                if abi_constraints:
                    phase4b_result = checker._retry_with_iterative_abi_constraints(
                        ctx, abi_constraints, retry_count=retry_count + 1
                    )
                    if phase4b_result is not None:
                        result = phase4b_result
                        p4b_transition = checker._get_transition_reason(result, retry_with_type_fix)
                        checker._record_attempt_from_result(
                            debug_trace,
                            attempt_id,
                            retry_count + 1,
                            "P4B_MIPS64_SPURIOUS",
                            result,
                            p4b_transition,
                            type_fix_result,
                        )
                        attempt_id += 1

                        if result.is_equivalent is True:
                            checker._debug_print(
                                f"Phase 4-B: EQUIVALENT after MIPS64 ABI retry (from {phase_id.value})"
                            )
                            return _attach_trace_and_return(
                                result, debug_trace, start_time, True
                            )
                        result, attempt_id, did_attempt = _maybe_retry_sat_return_type_fix(
                            checker,
                            ctx,
                            result,
                            debug_trace,
                            attempt_id,
                            retry_count + 2,
                            type_fixer1,
                            type_fixer2,
                            retry_with_type_fix,
                        )
                        attempted_return_type_fix = attempted_return_type_fix or did_attempt
                        if result.is_equivalent is True:
                            checker._debug_print(
                                f"Phase 4-C: EQUIVALENT after return type retry (from {phase_id.value})"
                            )
                            return _attach_trace_and_return(
                                result, debug_trace, start_time, True
                            )
            else:
                checker._debug_print("Phase 4-B: Skipped")

            if result.is_equivalent is False:
                result, attempt_id, did_attempt = _maybe_retry_sat_return_type_fix(
                    checker,
                    ctx,
                    result,
                    debug_trace,
                    attempt_id,
                    retry_count + 1,
                    type_fixer1,
                    type_fixer2,
                    retry_with_type_fix,
                )
                attempted_return_type_fix = attempted_return_type_fix or did_attempt
                if result.is_equivalent is True:
                    checker._debug_print(
                        f"Phase 4-C: EQUIVALENT after return type retry (from {phase_id.value})"
                    )
                    return _attach_trace_and_return(result, debug_trace, start_time, True)

            if result.is_equivalent is False:
                if (
                    attempted_return_type_fix
                    and retry_with_type_fix
                    and type_fixer1 is not None
                    and type_fixer2 is not None
                ):
                    result, attempt_id = _run_phase4a_tail(
                        checker,
                        ctx,
                        result,
                        debug_trace,
                        start_time,
                        retry_count,
                        attempt_id,
                        type_fixer1,
                        type_fixer2,
                        retry_with_type_fix,
                    )
                    if result.debug_trace is not None:
                        return result
                checker._debug_print(f"Phase {phase_id.value}: NOT EQUIVALENT - stopping")
                return _attach_trace_and_return(result, debug_trace, start_time, False)

        should_retry = checker.phase_handler.should_retry(result)
        retry_reason = checker.phase_handler.get_retry_reason(result)
        checker._debug_print(f"Phase {phase_id.value} result: {retry_reason}")

        if not should_retry:
            return _attach_trace_and_return(result, debug_trace, start_time, None)

        checker._debug_print(f"Proceeding to next phase ({retry_reason})")

    if retry_with_type_fix and type_fixer1 and type_fixer2 and result is not None:
        result, attempt_id = _run_phase4a_tail(
            checker,
            ctx,
            result,
            debug_trace,
            start_time,
            retry_count,
            attempt_id,
            type_fixer1,
            type_fixer2,
            retry_with_type_fix,
        )
        if result.debug_trace is not None:
            return result

    checker._debug_print("=" * 60)
    checker._debug_print("Final Result (end of phase plan)")
    checker._debug_print("=" * 60)

    if result is None:
        raise RuntimeError("No phase was executed: phase_plan is empty or no result was produced")

    return _attach_trace_and_return(result, debug_trace, start_time, result.is_equivalent)


def _run_phase4a_tail(
    checker,
    ctx: PhaseContext,
    result,
    debug_trace: DebugTrace,
    start_time: float,
    retry_count: int,
    attempt_id: int,
    type_fixer1,
    type_fixer2,
    retry_with_type_fix: bool,
):
    phase4a_spec = PhaseSpec(PhaseID.P4A_MIPS64_ABI, "MIPS64 ABI param fix (conservative)")
    phase_timeline = phase_timeline_of(checker)

    checker._debug_print("=" * 60)
    checker._debug_print(f"Phase {PhaseID.P4A_MIPS64_ABI.value}: {phase4a_spec.description}")
    checker._debug_print("=" * 60)

    # applied=False なら attempt を作らない phase なので、ここでは id を予約しない。
    phase_timeline.begin(
        PhaseID.P4A_MIPS64_ABI.value, reason_before=unknown_reason_ids(result)
    )
    with phase_timeline.measure("phase_fix"):
        phase_result = checker.phase_handler.execute_phase(
            phase4a_spec, ctx, type_fixer1, type_fixer2, checker._get_params_via_decompile
        )
    phase_timeline.record_phase_result(phase_result)

    if not phase_result.applied:
        phase_timeline.end(reason_after=unknown_reason_ids(result))
        return result, attempt_id

    # ここから先は必ずこの attempt_id で attempt を記録する。
    phase_timeline.record_attempt_id(attempt_id)
    retry_count += 1
    ctx.type_fix_result.retry_phase = phase_result.retry_name

    analysis1, analysis2, result = checker._selective_reanalysis_and_check(
        ctx, phase_result, retry_count=retry_count
    )
    phase_record = phase_timeline.end(reason_after=unknown_reason_ids(result))
    ctx.analysis1 = analysis1
    ctx.analysis2 = analysis2

    will_try_phase4b = False
    if result.is_equivalent is False:
        abi_constraints_check = checker.phase_handler.run_phase4_mips64_retry(result, ctx)
        will_try_phase4b = abi_constraints_check is not None

    transition_reason = checker._get_transition_reason(
        result, retry_with_type_fix, PhaseID.P4A_MIPS64_ABI.value, will_try_phase4b
    )
    checker._record_attempt_from_result(
        debug_trace,
        attempt_id,
        retry_count,
        PhaseID.P4A_MIPS64_ABI.value,
        result,
        transition_reason,
        ctx.type_fix_result,
        phase_diagnostics=phase_record,
    )
    attempt_id += 1

    if result.is_equivalent is True:
        checker._debug_print(f"Phase {PhaseID.P4A_MIPS64_ABI.value}: EQUIVALENT")
        return _attach_trace_and_return(result, debug_trace, start_time, True), attempt_id

    if result.is_equivalent is False and retry_with_type_fix and will_try_phase4b:
        abi_constraints = checker.phase_handler.run_phase4_mips64_retry(result, ctx)
        if abi_constraints:
            phase4b_result = checker._retry_with_iterative_abi_constraints(
                ctx, abi_constraints, retry_count=retry_count + 1
            )
            if phase4b_result is not None:
                result = phase4b_result
                p4b_transition = checker._get_transition_reason(result, retry_with_type_fix)
                checker._record_attempt_from_result(
                    debug_trace,
                    attempt_id,
                    retry_count + 1,
                    "P4B_MIPS64_SPURIOUS",
                    result,
                    p4b_transition,
                    ctx.type_fix_result,
                )
                attempt_id += 1

                if result.is_equivalent is True:
                    checker._debug_print(
                        "Phase 4-B: EQUIVALENT after MIPS64 ABI retry (from Phase 4-A)"
                    )
                    return _attach_trace_and_return(result, debug_trace, start_time, True), attempt_id
                result, attempt_id, did_attempt = _maybe_retry_sat_return_type_fix(
                    checker,
                    ctx,
                    result,
                    debug_trace,
                    attempt_id,
                    retry_count + 2,
                    type_fixer1,
                    type_fixer2,
                    retry_with_type_fix,
                )
                if result.is_equivalent is False and did_attempt:
                    result, attempt_id = _run_phase4a_tail(
                        checker,
                        ctx,
                        result,
                        debug_trace,
                        start_time,
                        retry_count + 2,
                        attempt_id,
                        type_fixer1,
                        type_fixer2,
                        retry_with_type_fix,
                    )
                    if result.debug_trace is not None:
                        return result, attempt_id
                if result.is_equivalent is True:
                    checker._debug_print(
                        "Phase 4-C: EQUIVALENT after return type retry (from Phase 4-A)"
                    )
                    return _attach_trace_and_return(result, debug_trace, start_time, True), attempt_id

    return result, attempt_id


def _maybe_retry_sat_return_type_fix(
    checker,
    ctx: PhaseContext,
    result,
    debug_trace: DebugTrace,
    attempt_id: int,
    retry_count: int,
    type_fixer1,
    type_fixer2,
    retry_with_type_fix: bool,
):
    """SAT のまま残った戻り値型疑義に対して、限定的に型修正リトライする。"""
    if not retry_with_type_fix:
        return result, attempt_id, False

    if result.is_equivalent is not False:
        return result, attempt_id, False

    if ctx.analysis1 is None or ctx.analysis2 is None:
        return result, attempt_id, False

    should_fix1 = checker.phase_handler.should_fix_return_type(
        ctx.analysis1,
        ctx.analysis2,
    )
    should_fix2 = checker.phase_handler.should_fix_return_type(
        ctx.analysis2,
        ctx.analysis1,
    )
    if not (should_fix1 or should_fix2):
        return result, attempt_id, False

    checker._debug_print(
        "Phase 4-C: SAT persists, attempting suspicious return type fix"
    )

    phase_timeline = phase_timeline_of(checker)
    # applied=False なら attempt を作らない phase なので、ここでは id を予約しない。
    phase_timeline.begin(
        "P4C_RETURN_TYPE_FIX",
        retry_name="sat_return_type_fix",
        reason_before=unknown_reason_ids(result),
    )
    with phase_timeline.measure("phase_fix"):
        applied, changed1, changed2 = checker.phase_handler.run_phase2_return_type_fix(
            ctx,
            type_fixer1,
            type_fixer2,
        )
    phase_timeline.record_applied(applied, changed1, changed2)
    if not applied:
        phase_timeline.end(reason_after=unknown_reason_ids(result))
        checker._debug_print("Phase 4-C: Return type fix was not applied")
        return result, attempt_id, True

    # ここから先は必ずこの attempt_id で attempt を記録する。
    phase_timeline.record_attempt_id(attempt_id)

    ctx.type_fix_result.retry_phase = "sat_return_type_fix"
    phase_result = PhaseResult(
        PhaseID.P2_PATTERN_INT,
        applied=True,
        retry_name="sat_return_type_fix",
        changed_binary1=changed1,
        changed_binary2=changed2,
    )
    analysis1, analysis2, result = checker._selective_reanalysis_and_check(
        ctx, phase_result, retry_count=retry_count
    )
    phase_record = phase_timeline.end(reason_after=unknown_reason_ids(result))
    ctx.analysis1 = analysis1
    ctx.analysis2 = analysis2

    transition_reason = checker._get_transition_reason(
        result, retry_with_type_fix, phase_id="P4C_RETURN_TYPE_FIX"
    )
    checker._record_attempt_from_result(
        debug_trace,
        attempt_id,
        retry_count,
        "P4C_RETURN_TYPE_FIX",
        result,
        transition_reason,
        ctx.type_fix_result,
        phase_diagnostics=phase_record,
    )
    return result, attempt_id + 1, True


def _finalize_if_terminal(checker, result, debug_trace, start_time, phase_name):
    if result.is_equivalent is True:
        checker._debug_print(f"Phase {phase_name}: EQUIVALENT - stopping")
        return _attach_trace_and_return(result, debug_trace, start_time, True)

    if result.has_critical_error():
        checker._debug_print(f"Phase {phase_name}: Critical error - {result.error_message}")
        finalized = _attach_trace_and_return(result, debug_trace, start_time, None)
        finalized.debug_trace.error_message = result.error_message
        return finalized

    return None


def _attach_trace_and_return(result, debug_trace: DebugTrace, start_time: float, final_result):
    result.total_time = time.time() - start_time
    result.debug_trace = debug_trace
    debug_trace.final_result = final_result
    debug_trace.total_time = result.total_time
    if result.error_message:
        debug_trace.error_message = result.error_message
    return result
