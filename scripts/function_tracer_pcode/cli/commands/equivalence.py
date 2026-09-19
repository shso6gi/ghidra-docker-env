# -*- coding: utf-8 -*-
"""Equivalence-mode CLI helpers.

The semantic input of an equivalence check is exactly the two binaries given to
``--equiv``.  Files adjacent to those binaries (in particular the EqBench
``newV.c`` / ``new.c`` sources) are never read here: they are inputs of the
benchmark evaluation oracle, not of the judgement, its provenance, or the signed
execution identity (Issue #122).
"""

import json
import hashlib
import os
import stat
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

from scripts.function_tracer_pcode.ghidra.pyghidra_support import (
    load_pyghidra,
    start_headless_pyghidra,
)
from scripts.function_tracer_pcode.config import apply_runtime_environment
from scripts.function_tracer_pcode.checker.result import EquivalenceResult
# Issue #124 PR-124-B: `result_emit` は結果 JSON の外（journal）にだけ残す区間。
from scripts.function_tracer_pcode.core.stage_journal import (
    journal_stage_end,
    journal_stage_start,
)
from scripts.function_tracer_pcode.reporting import output_result
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.cli.commands.analyze import get_target_functions


class ProgramImportError(RuntimeError):
    """Raised when Ghidra cannot import one of the input binaries."""


def _binary_content_identity(binary_path: str):
    if not os.path.isfile(binary_path):
        return None
    digest = hashlib.sha256()
    with open(binary_path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return ("sha256", digest.hexdigest())


def _safe_close_context(manager) -> None:
    """Best-effort cleanup that tolerates a stopped JVM during interruption."""
    if manager is None:
        return
    try:
        manager.__exit__(None, None, None)
    except Exception as exc:
        exc_text = str(exc).lower()
        if "jvm is not running" in exc_text or "java virtual machine is not running" in exc_text:
            return
        raise


def _get_binary_ids_arg(args):
    value = getattr(args, "binary_ids", None)
    if isinstance(value, (list, tuple)) and len(value) == 2:
        return value[0], value[1]
    return None, None


def _journal_run_context(args):
    """journal の 1 行目に残す pair の識別情報（Issue #124 PR-124-B）。

    結果 JSON が出ない pair でも「どのペアの journal か」が分かるようにする。
    診断なので判定には使わない。値は型を確かめてから入れる（診断の組み立てで
    例外を出して判定経路を壊さないため）。
    """
    def _strings(value):
        if not isinstance(value, (list, tuple)):
            return []
        return [item for item in value if isinstance(item, str)]

    context = {"binaries": _strings(getattr(args, "equiv", None))}
    binary_ids = _strings(getattr(args, "binary_ids", None))
    if len(binary_ids) == 2:
        context["binary_ids"] = binary_ids
    functions = _strings(getattr(args, "functions", None))
    if functions:
        context["functions"] = functions
    return context


def _exception_chain_text(exc: BaseException) -> str:
    """Return a compact exception-chain string that includes Java exception text."""
    parts = []
    current: BaseException | None = exc
    seen: set[int] = set()
    while current is not None and id(current) not in seen:
        seen.add(id(current))
        parts.append(f"{type(current).__name__}: {current}")
        current = current.__cause__ or current.__context__
    return " | caused by: ".join(parts)


def _binary_path_diagnostics(path: str) -> str:
    binary_path = Path(path)
    lines = [
        f"path={path}",
        f"absolute={binary_path.resolve(strict=False)}",
        f"cwd={Path.cwd()}",
        f"tmpdir={tempfile.gettempdir()}",
        f"TMPDIR={os.environ.get('TMPDIR', '<unset>')}",
        f"exists={binary_path.exists()}",
        f"is_file={binary_path.is_file()}",
    ]
    try:
        st = binary_path.stat()
        mode = stat.filemode(st.st_mode)
        lines.extend(
            [
                f"size={st.st_size}",
                f"mode={mode}",
                f"uid={st.st_uid}",
                f"gid={st.st_gid}",
            ]
        )
    except OSError as exc:
        lines.append(f"stat_error={type(exc).__name__}: {exc}")
    try:
        with binary_path.open("rb") as handle:
            header = handle.read(16)
        lines.append(f"read_probe=ok first16={header.hex()}")
    except OSError as exc:
        lines.append(f"read_probe_error={type(exc).__name__}: {exc}")
    return "; ".join(lines)


def _to_java_byte_array(data: bytes) -> Any:
    """Convert Python bytes to a Java byte[] so JPype selects source(byte[])."""
    try:
        import jpype

        return jpype.JArray(jpype.JByte)(data)
    except Exception:
        return data


def _load_program_context(
    pyghidra: Any,
    project: Any,
    binary_path: str,
    import_name: str,
    *,
    quiet: bool,
):
    """Load a program, retrying with byte-array source if Ghidra's file provider fails."""
    first_cm = None
    try:
        first_cm = (
            pyghidra.program_loader()
            .project(project)
            .source(binary_path)
            .name(import_name)
            .load()
        )
        return first_cm, first_cm.__enter__()
    except Exception as first_exc:
        _safe_close_context(first_cm)
        diagnostics = _binary_path_diagnostics(binary_path)
        binary_file = Path(binary_path)
        if not binary_file.is_file():
            raise ProgramImportError(
                "Ghidra import failed and the source is not a regular file: "
                f"{_exception_chain_text(first_exc)}; diagnostics: {diagnostics}"
            ) from first_exc

        try:
            binary_bytes = binary_file.read_bytes()
        except OSError as read_exc:
            raise ProgramImportError(
                "Ghidra import failed and Python could not read the source for "
                f"byte-array fallback: {_exception_chain_text(first_exc)}; "
                f"fallback_read_error={type(read_exc).__name__}: {read_exc}; "
                f"diagnostics: {diagnostics}"
            ) from read_exc

        fallback_cm = None
        try:
            fallback_cm = (
                pyghidra.program_loader()
                .project(project)
                .source(_to_java_byte_array(binary_bytes))
                .name(import_name)
                .load()
            )
            if not quiet:
                print(
                    "[EquivalenceCLI] Ghidra file-provider import failed; "
                    f"loaded {binary_path} via byte-array fallback."
                )
                print(f"[EquivalenceCLI] Original import error: {_exception_chain_text(first_exc)}")
            return fallback_cm, fallback_cm.__enter__()
        except Exception as fallback_exc:
            _safe_close_context(fallback_cm)
            raise ProgramImportError(
                "Ghidra import failed for file-provider source and byte-array "
                f"fallback: file_error={_exception_chain_text(first_exc)}; "
                f"fallback_error={_exception_chain_text(fallback_exc)}; "
                f"diagnostics: {diagnostics}"
            ) from fallback_exc


def _emit_import_error_result(
    args,
    *,
    binary1_path: str,
    binary2_path: str,
    func_name1: str,
    func_name2: str,
    error_message: str,
    error_kind: str = "PROGRAM_IMPORT_ERROR",
    start_time: float,
    binary1_content_identity=None,
    binary2_content_identity=None,
) -> None:
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name=func_name1,
        function2_name=func_name2,
        binary1_name=Path(binary1_path).name,
        binary2_name=Path(binary2_path).name,
        solver_results=ParallelResult(results=[]),
        binary1_content_identity=binary1_content_identity,
        binary2_content_identity=binary2_content_identity,
        total_time=time.time() - start_time,
        error_message=error_message,
    )
    from scripts.function_tracer_pcode.authority.contracts import authority_digest
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        attach_canonical_decision,
        issue_infrastructure_error_decision,
    )

    result_occurrence_id = "import-error-" + authority_digest({
        "binary1_path": binary1_path,
        "binary2_path": binary2_path,
        "function_name1": func_name1,
        "function_name2": func_name2,
        "binary1_content_identity": binary1_content_identity,
        "binary2_content_identity": binary2_content_identity,
    })[:32]
    attach_canonical_decision(
        result,
        issue_infrastructure_error_decision(
            result_occurrence_id=result_occurrence_id,
            error_kind=error_kind,
            error_artifact_digest=authority_digest({
                "result_occurrence_id": result_occurrence_id,
                "error_message": error_message,
            }),
        ),
    )
    from scripts.function_tracer_pcode.authority.decision.canonical_result import (
        attach_durable_error_finalization,
        build_canonical_result_finalization_bundle,
        persist_canonical_result_envelope,
    )

    error_artifact_digest = authority_digest({
        "result_occurrence_id": result_occurrence_id,
        "error_message": error_message,
    })
    attach_durable_error_finalization(
        result,
        execution_payload={
            "binary1_id": binary1_path,
            "binary2_id": binary2_path,
            "binary1_content_identity": binary1_content_identity,
            "binary2_content_identity": binary2_content_identity,
            "function_name1": func_name1,
            "function_name2": func_name2,
            "error_stage": "cli_import",
        },
        error_kind=error_kind,
        error_artifact_digest=error_artifact_digest,
    )
    # Issue #124 PR-124-B: ERROR 経路の emission も同じ区間名で journal に残す
    # （journal を持つ pair が結果 JSON の有無で欠けないようにする）。
    emission_started = time.monotonic()
    journal_stage_start("result_emit", {"kind": "emission", "path": "import_error"})
    result_payload = result.to_dict()
    evidence, session = result._canonical_finalization_context
    bundle = build_canonical_result_finalization_bundle(
        result_payload_preimage=result_payload, evidence=evidence, session=session
    )
    result.canonical_result_finalization_bundle = bundle
    result_payload["canonical_result_finalization_bundle"] = bundle
    persist_canonical_result_envelope(result_payload)
    output_result(
        result.to_string(
            verbose=getattr(args, "verbose", False),
            show_phase_usage=getattr(args, "debug", False),
        ),
        args.output,
        args.quiet,
    )
    json_payload = json.dumps(result_payload, ensure_ascii=False, sort_keys=True)
    output_result(
        "\n".join(
            (
                "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
                json_payload,
                "=== EQUIVALENCE_RESULT_JSON_END ===",
            )
        ),
        args.output,
        args.quiet,
    )
    journal_stage_end("result_emit", time.monotonic() - emission_started, {
        "kind": "emission", "path": "import_error",
    })
    from scripts.function_tracer_pcode.authority.contracts import Outcome
    from scripts.function_tracer_pcode.authority.decision.production_cutover import CLI_EXIT_MATRIX

    sys.exit(CLI_EXIT_MATRIX[Outcome.ERROR])


def run_equivalence_check(args):
    """等価性判定を実行する。

    入力は ``args.equiv`` の 2 バイナリのみ。バイナリ隣接ファイルは読まない
    （Issue #122）。
    """
    start_time = time.time()
    from scripts.function_tracer_pcode.checker.diagnostics import (
        StageClock,
        attach_failure_diagnostics,
        attach_stage_timing,
    )
    from scripts.function_tracer_pcode.checker.cause_aggregate import attach_cause_aggregate
    from scripts.function_tracer_pcode.core.errors import (
        reset_pair_failure_scopes,
        reset_swallowed_exceptions,
    )

    # Issue #125: 握り潰した例外の集計はペア 1 件の実行ごとに取り直す。
    reset_swallowed_exceptions()
    # Issue #106 PR-106-0: pair 台帳 stack も同じ理由で空から始める。process =
    # pair 1 件なので通常は既に空だが、前の pair の状態を引き継がないことを
    # 入口でも保証する（台帳 scope 自体の破棄と二重の保証）。
    reset_pair_failure_scopes()
    stage_clock = StageClock()

    # Issue #124 PR-124-B: journal と stack dump handler は **in-process の JVM を
    # 起動する前**に設置する（`start_headless_pyghidra` はこの下）。handler の
    # readiness は `faulthandler.register()` が成功したことだけを根拠にし、
    # 失敗しても判定にも終了状態にも影響しない。診断 signal の送信は行わない
    # （supervisor 側の責務、PR-124-C）。
    from scripts.function_tracer_pcode.cli.pair_diagnostics import (
        install_pair_diagnostics,
    )

    install_pair_diagnostics(args, context=_journal_run_context(args))

    def _get_bool_arg(name: str, default: bool = False) -> bool:
        value = getattr(args, name, default)
        return value if isinstance(value, bool) else default

    def _get_choice_arg(name: str, allowed: set[str], default: str) -> str:
        value = getattr(args, name, default)
        return value if isinstance(value, str) and value in allowed else default

    binary1_path, binary2_path = args.equiv
    binary1_content_identity = _binary_content_identity(binary1_path)
    binary2_content_identity = _binary_content_identity(binary2_path)
    binary1_id, binary2_id = _get_binary_ids_arg(args)
    try:
        runtime_env = apply_runtime_environment()
        pyghidra = load_pyghidra()
    except Exception as exc:
        _emit_import_error_result(
            args,
            binary1_path=binary1_path,
            binary2_path=binary2_path,
            func_name1="<startup>",
            func_name2="<startup>",
            error_message=_exception_chain_text(exc),
            error_kind="CLI_STARTUP_ERROR",
            start_time=start_time,
            binary1_content_identity=binary1_content_identity,
            binary2_content_identity=binary2_content_identity,
        )

    from scripts.function_tracer_pcode.checker import EquivalenceChecker, TypeFixerConfig

    function_names = get_target_functions(args)

    if len(function_names) == 0:
        _emit_import_error_result(
            args,
            binary1_path=binary1_path,
            binary2_path=binary2_path,
            func_name1="<missing>",
            func_name2="<missing>",
            error_message="function name is required (-f)",
            error_kind="CLI_ARGUMENT_ERROR",
            start_time=start_time,
            binary1_content_identity=binary1_content_identity,
            binary2_content_identity=binary2_content_identity,
        )
    if len(function_names) == 1:
        func_name1 = func_name2 = function_names[0]
    else:
        func_name1 = function_names[0]
        func_name2 = function_names[1]

    retry_with_type_fix = not getattr(args, "no_retry_phases", False)
    strategy = getattr(args, "strategy", "pairwise")

    if not args.quiet:
        print("等価性判定モード")
        print(f"  Binary 1: {binary1_path}")
        print(f"  Binary 2: {binary2_path}")
        print(f"  Function 1: {func_name1}")
        print(f"  Function 2: {func_name2}")
        print(f"  Strategy: {strategy}")
        print(f"  Normalize mode: {_get_choice_arg('normalize_mode', {'off', 'safe', 'full'}, 'safe')}")
        print(
            "  Fact normalization: "
            f"{'enabled' if _get_bool_arg('enable_fact_normalization', False) else 'disabled'}"
        )
        print(
            "  Template abstraction: "
            f"{'enabled' if _get_bool_arg('enable_template_abstraction', False) else 'disabled'}"
        )
        print(f"  Timeout: {args.equiv_timeout}秒")
        print(
            f"  Recovery phases: {'disabled' if getattr(args, 'no_retry_phases', False) else 'enabled'}"
        )
        print(
            "  Completed recovery proofs: "
            f"{'disabled' if getattr(args, 'no_completed_recovery_proofs', False) else 'enabled'}"
        )
        print(
            "  FP non-NaN assumption: "
            f"{'enabled' if getattr(args, 'assume_fp_non_nan', False) else 'disabled'}"
        )
        if getattr(args, "assume_fp_non_nan", False):
            print("  FP non-NaN scope: 32bit/64bit float args only")
        print(
            "  errno observation: "
            f"{'enabled' if getattr(args, 'observe_errno', False) else 'disabled'}"
        )
        print(
            "  fenv observation: "
            f"{'enabled' if getattr(args, 'observe_fenv', False) else 'disabled'}"
        )
        print()

    stage_clock.mark("cli_preamble", time.time() - start_time)
    with stage_clock.timed("jvm_start"):
        start_headless_pyghidra(
            pyghidra,
            install_dir=(
                Path(runtime_env.ghidra_install_dir)
                if runtime_env.ghidra_install_dir
                else None
            ),
        )

    type_fixer_config = TypeFixerConfig()
    pairwise_timeout = getattr(args, "pairwise_timeout", 5)
    pairwise_timeout_hard = getattr(args, "pairwise_timeout_hard", 30)
    monolithic_timeout = getattr(args, "monolithic_timeout", None)
    if not isinstance(monolithic_timeout, int) or isinstance(monolithic_timeout, bool):
        monolithic_timeout = None
    monolithic_query_mode = _get_choice_arg(
        "monolithic_query_mode", {"split", "legacy"}, "split"
    )
    pairwise_save_unknown = getattr(args, "pairwise_save_unknown", False)
    pairwise_unknown_dir = getattr(args, "pairwise_unknown_dir", None)
    normalization_mode = _get_choice_arg("normalize_mode", {"off", "safe", "full"}, "safe")
    enable_fact_normalization = _get_bool_arg("enable_fact_normalization", False)
    enable_template_abstraction = _get_bool_arg("enable_template_abstraction", False)

    checker = EquivalenceChecker(
        timeout=args.equiv_timeout,
        debug=args.debug,
        type_fixer_config=type_fixer_config,
        strategy=strategy,
        pairwise_timeout=pairwise_timeout,
        pairwise_timeout_hard=pairwise_timeout_hard,
        monolithic_timeout=monolithic_timeout,
        monolithic_query_mode=monolithic_query_mode,
        pairwise_save_unknown=pairwise_save_unknown,
        pairwise_unknown_dir=pairwise_unknown_dir,
        normalization_mode=normalization_mode,
        enable_fact_normalization=enable_fact_normalization,
        enable_template_abstraction=enable_template_abstraction,
        enable_completed_recovery_proofs=not getattr(args, "no_completed_recovery_proofs", False),
        assume_fp_non_nan=getattr(args, "assume_fp_non_nan", False),
        observes_errno=getattr(args, "observe_errno", False),
        observes_fenv=getattr(args, "observe_fenv", False),
        identical_fast_path=not getattr(args, "no_identical_fast_path", False),
    )

    available_solvers = checker.solver_runner.get_available_solvers()
    if not args.quiet:
        print(f"利用可能なソルバー: {', '.join(available_solvers) if available_solvers else 'なし'}")
        print()

    if not available_solvers:
        _emit_import_error_result(
            args,
            binary1_path=binary1_path,
            binary2_path=binary2_path,
            func_name1=func_name1,
            func_name2=func_name2,
            error_message="no SMT solver is available",
            error_kind="NO_SMT_SOLVER",
            start_time=start_time,
            binary1_content_identity=binary1_content_identity,
            binary2_content_identity=binary2_content_identity,
        )

    try:
        with tempfile.TemporaryDirectory() as temp_dir:
            with stage_clock.timed("project_open"):
                project_cm = pyghidra.open_project(temp_dir, "EquivCheckProject", create=True)
                project = project_cm.__enter__()
            try:
                with stage_clock.timed("import_binary1"):
                    result1_cm, result1 = _load_program_context(
                        pyghidra,
                        project,
                        binary1_path,
                        "binary1",
                        quiet=args.quiet,
                    )
                try:
                    program1 = result1.getPrimaryDomainObject()
                    with stage_clock.timed("auto_analyze_binary1"):
                        pyghidra.analyze(program1)

                    with stage_clock.timed("import_binary2"):
                        result2_cm, result2 = _load_program_context(
                            pyghidra,
                            project,
                            binary2_path,
                            "binary2",
                            quiet=args.quiet,
                        )
                    try:
                        program2 = result2.getPrimaryDomainObject()
                        with stage_clock.timed("auto_analyze_binary2"):
                            pyghidra.analyze(program2)

                        check_started = time.monotonic()
                        # Issue #124: region scope はペア 1 件につき 1 回だけ、
                        # stage plan より外側で開く。この内側で開かれた region
                        # （check / obligation_build / query_build / 解析 sub-stage
                        # …）は 1 つの木に積まれ、二重計上されない。
                        with stage_clock.scope():
                            result = checker.check_from_binaries(
                                program1,
                                program2,
                                func_name1,
                                func_name2,
                                decompile_timeout=args.timeout,
                                save_formula=args.save_formula,
                                retry_with_type_fix=retry_with_type_fix,
                                binary1_id=binary1_id,
                                binary2_id=binary2_id,
                                binary1_content_identity=binary1_content_identity,
                                binary2_content_identity=binary2_content_identity,
                            )
                        stage_clock.mark("check", time.monotonic() - check_started)
                    finally:
                        with stage_clock.timed("close_programs"):
                            _safe_close_context(result2_cm)
                finally:
                    with stage_clock.timed("close_programs"):
                        _safe_close_context(result1_cm)
            finally:
                with stage_clock.timed("close_programs"):
                    _safe_close_context(project_cm)
    except KeyboardInterrupt:
        if not args.quiet:
            print("\nInterrupted by user.")
        sys.exit(130)
    except ProgramImportError as exc:
        _emit_import_error_result(
            args,
            binary1_path=binary1_path,
            binary2_path=binary2_path,
            func_name1=func_name1,
            func_name2=func_name2,
            error_message=str(exc),
            start_time=start_time,
            binary1_content_identity=binary1_content_identity,
            binary2_content_identity=binary2_content_identity,
        )

    attach_stage_timing(result, stage_clock)
    # Issue #125 / #128: 添付順は attach_stage_timing -> attach_failure_diagnostics
    # -> attach_cause_aggregate -> to_string -> to_dict -> bundle。診断は
    # preimage を組む前に確定させる（確定後に payload を書き換えない）。
    attach_failure_diagnostics(result)
    attach_cause_aggregate(result)
    emission_started = time.monotonic()
    # Issue #124 PR-124-B: `result_emit` は `to_dict()` を呼ぶ**前**から JSON の
    # 書き出し完了までを囲む（結果の描画・正準化・envelope 永続化が入る区間で、
    # 結果 JSON 自身の中には入れられない）。journal にしか出さないので添付順
    # （stage timing -> failures -> cause aggregate -> to_string -> to_dict ->
    # bundle -> JSON write）も serialization 契約も変えない。ここで例外が出た
    # 場合は `stage_end` が書かれないままになり、それが「emission の途中で
    # 落ちた」という観測になる。
    journal_stage_start("result_emit", {
        "kind": "emission",
        "emit_result_json": _get_bool_arg("emit_result_json", False),
    })
    output_content = result.to_string(
        verbose=args.verbose,
        show_phase_usage=args.debug,
    )
    output_result(output_content, args.output, args.quiet)
    render_seconds = time.monotonic() - emission_started

    if _get_bool_arg("emit_result_json", False):
        result_payload = result.to_dict()
        from scripts.function_tracer_pcode.authority.decision.canonical_result import (
            build_canonical_result_finalization_bundle,
            persist_canonical_result_envelope,
        )

        finalization_context = getattr(
            result, "_canonical_finalization_context", None
        )
        if finalization_context is not None:
            evidence, session = finalization_context
            bundle = build_canonical_result_finalization_bundle(
                result_payload_preimage=result_payload,
                evidence=evidence,
                session=session,
            )
            result.canonical_result_finalization_bundle = bundle
            result_payload["canonical_result_finalization_bundle"] = bundle

        persist_canonical_result_envelope(result_payload)
        json_payload = json.dumps(result_payload, ensure_ascii=False, sort_keys=True)
        json_content = "\n".join(
            (
                "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
                json_payload,
                "=== EQUIVALENCE_RESULT_JSON_END ===",
            )
        )
        output_result(json_content, args.output, args.quiet)

    journal_stage_end("result_emit", time.monotonic() - emission_started, {
        "kind": "emission",
        "render_seconds": round(render_seconds, 6),
    })

    if not args.quiet:
        # 結果の描画・JSON 化・envelope 永続化に掛かった時間。結果 JSON の中には
        # 入れられない（JSON 自体の生成時間なので）ためログ行として残す。
        print(
            "[EquivalenceCLI] Result emission seconds: "
            f"render={render_seconds:.3f} total={time.monotonic() - emission_started:.3f}"
        )

    if args.save_formula and result.smt_formula:
        if not args.quiet:
            print("\nGenerated SMT Formula:")
            print("-" * 70)
            print(result.smt_formula)
            print("-" * 70)

        if args.output:
            smt_output = args.output.rsplit(".", 1)[0] + ".smt2"
            with open(smt_output, "w") as handle:
                handle.write(result.smt_formula)
            print(f"SMT formula saved to: {smt_output}")

    if getattr(result, "decision_receipt", None) is not None:
        from scripts.function_tracer_pcode.authority.decision.production_cutover import (
            CLI_EXIT_MATRIX,
            outcome_from_result,
        )

        sys.exit(CLI_EXIT_MATRIX[outcome_from_result(result)])
    if result.is_equivalent is True:
        sys.exit(0)
    if result.is_equivalent is False:
        sys.exit(1)
    sys.exit(2)
