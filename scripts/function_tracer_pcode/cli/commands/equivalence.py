# -*- coding: utf-8 -*-
"""Equivalence-mode CLI helpers."""

import sys
import json
import tempfile
from pathlib import Path

from .._pyghidra_support import load_pyghidra, start_headless_pyghidra
from ...config import apply_runtime_environment
from ...io import output_result
from .analyze import get_target_functions


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


def run_equivalence_check(args):
    """等価性判定を実行する。"""
    def _get_bool_arg(name: str, default: bool = False) -> bool:
        value = getattr(args, name, default)
        return value if isinstance(value, bool) else default

    def _get_choice_arg(name: str, allowed: set[str], default: str) -> str:
        value = getattr(args, name, default)
        return value if isinstance(value, str) and value in allowed else default

    runtime_env = apply_runtime_environment()
    pyghidra = load_pyghidra()

    from ...equivalence import EquivalenceChecker, TypeFixerConfig

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
                loader1 = pyghidra.program_loader().project(project).source(binary1_path).name("binary1")
                result1_cm = loader1.load()
                result1 = result1_cm.__enter__()
                try:
                    program1 = result1.getPrimaryDomainObject()
                    pyghidra.analyze(program1)

                    loader2 = pyghidra.program_loader().project(project).source(binary2_path).name("binary2")
                    result2_cm = loader2.load()
                    result2 = result2_cm.__enter__()
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
