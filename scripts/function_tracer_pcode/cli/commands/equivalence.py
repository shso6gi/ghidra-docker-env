# -*- coding: utf-8 -*-
"""Equivalence-mode CLI helpers."""

import json
import os
import stat
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

from .._pyghidra_support import load_pyghidra, start_headless_pyghidra
from ...config import apply_runtime_environment
from ...equivalence.result import EquivalenceResult
from ...io import output_result
from ...smt import ParallelResult
from .analyze import get_target_functions


class ProgramImportError(RuntimeError):
    """Raised when Ghidra cannot import one of the input binaries."""


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
    start_time: float,
) -> None:
    result = EquivalenceResult(
        is_equivalent=None,
        function1_name=func_name1,
        function2_name=func_name2,
        binary1_name=Path(binary1_path).name,
        binary2_name=Path(binary2_path).name,
        solver_results=ParallelResult(results=[]),
        total_time=time.time() - start_time,
        error_message=error_message,
    )
    output_result(
        result.to_string(
            verbose=getattr(args, "verbose", False),
            show_phase_usage=getattr(args, "debug", False),
        ),
        args.output,
        args.quiet,
    )
    if getattr(args, "emit_result_json", False):
        json_payload = json.dumps(result.to_dict(), ensure_ascii=False, sort_keys=True)
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
    sys.exit(1)


def run_equivalence_check(args):
    """等価性判定を実行する。"""
    start_time = time.time()

    def _get_bool_arg(name: str, default: bool = False) -> bool:
        value = getattr(args, name, default)
        return value if isinstance(value, bool) else default

    def _get_choice_arg(name: str, allowed: set[str], default: str) -> str:
        value = getattr(args, name, default)
        return value if isinstance(value, str) and value in allowed else default

    runtime_env = apply_runtime_environment()
    pyghidra = load_pyghidra()

    from ...equivalence import EquivalenceChecker, TypeFixerConfig
    from ...equivalence.source_declarations import infer_adjacent_c_return_type

    binary1_path, binary2_path = args.equiv
    binary1_id, binary2_id = _get_binary_ids_arg(args)
    function_names = get_target_functions(args)

    if len(function_names) == 0:
        print("Error: 関数名を指定してください（-f オプション）")
        sys.exit(1)
    if len(function_names) == 1:
        func_name1 = func_name2 = function_names[0]
    else:
        func_name1 = function_names[0]
        func_name2 = function_names[1]
    declared_return_type1 = infer_adjacent_c_return_type(binary1_path, func_name1)
    declared_return_type2 = infer_adjacent_c_return_type(binary2_path, func_name2)

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

    start_headless_pyghidra(
        pyghidra,
        install_dir=(
            Path(runtime_env.ghidra_install_dir)
            if runtime_env.ghidra_install_dir
            else None
        ),
    )

    type_fixer_config = TypeFixerConfig()
    enable_rewrite = not getattr(args, "no_rewrite", False)
    rewrite_direction = getattr(args, "rewrite_direction", "to_modulo")
    pairwise_timeout = getattr(args, "pairwise_timeout", 5)
    pairwise_timeout_hard = getattr(args, "pairwise_timeout_hard", 30)
    pairwise_save_unknown = getattr(args, "pairwise_save_unknown", False)
    pairwise_unknown_dir = getattr(args, "pairwise_unknown_dir", None)
    normalization_mode = _get_choice_arg("normalize_mode", {"off", "safe", "full"}, "safe")
    enable_fact_normalization = _get_bool_arg("enable_fact_normalization", False)
    enable_template_abstraction = _get_bool_arg("enable_template_abstraction", False)

    checker = EquivalenceChecker(
        timeout=args.equiv_timeout,
        debug=args.debug,
        type_fixer_config=type_fixer_config,
        enable_rewrite=enable_rewrite,
        rewrite_direction=rewrite_direction,
        strategy=strategy,
        pairwise_timeout=pairwise_timeout,
        pairwise_timeout_hard=pairwise_timeout_hard,
        pairwise_save_unknown=pairwise_save_unknown,
        pairwise_unknown_dir=pairwise_unknown_dir,
        normalization_mode=normalization_mode,
        enable_fact_normalization=enable_fact_normalization,
        enable_template_abstraction=enable_template_abstraction,
        enable_completed_recovery_proofs=not getattr(args, "no_completed_recovery_proofs", False),
        assume_fp_non_nan=getattr(args, "assume_fp_non_nan", False),
        observes_errno=getattr(args, "observe_errno", False),
        observes_fenv=getattr(args, "observe_fenv", False),
    )

    available_solvers = checker.solver_runner.get_available_solvers()
    if not args.quiet:
        print(f"利用可能なソルバー: {', '.join(available_solvers) if available_solvers else 'なし'}")
        print()

    if not available_solvers:
        print("Error: SMTソルバーが利用できません")
        print("以下のいずれかをインストールしてください:")
        print("  pip install z3-solver")
        print("  pip install pyboolector")
        print("  pip install yices")
        print("  pip install cvc5")
        sys.exit(1)

    try:
        with tempfile.TemporaryDirectory() as temp_dir:
            project_cm = pyghidra.open_project(temp_dir, "EquivCheckProject", create=True)
            project = project_cm.__enter__()
            try:
                result1_cm, result1 = _load_program_context(
                    pyghidra,
                    project,
                    binary1_path,
                    "binary1",
                    quiet=args.quiet,
                )
                try:
                    program1 = result1.getPrimaryDomainObject()
                    pyghidra.analyze(program1)

                    result2_cm, result2 = _load_program_context(
                        pyghidra,
                        project,
                        binary2_path,
                        "binary2",
                        quiet=args.quiet,
                    )
                    try:
                        program2 = result2.getPrimaryDomainObject()
                        pyghidra.analyze(program2)

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
                            declared_return_type1=declared_return_type1,
                            declared_return_type2=declared_return_type2,
                        )
                    finally:
                        _safe_close_context(result2_cm)
                finally:
                    _safe_close_context(result1_cm)
            finally:
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
        )

    output_content = result.to_string(
        verbose=args.verbose,
        show_phase_usage=args.debug,
    )
    output_result(output_content, args.output, args.quiet)

    if _get_bool_arg("emit_result_json", False):
        json_payload = json.dumps(result.to_dict(), ensure_ascii=False, sort_keys=True)
        json_content = "\n".join(
            (
                "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
                json_payload,
                "=== EQUIVALENCE_RESULT_JSON_END ===",
            )
        )
        output_result(json_content, args.output, args.quiet)

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

    if result.is_equivalent is True:
        sys.exit(0)
    if result.is_equivalent is False:
        sys.exit(1)
    sys.exit(2)
