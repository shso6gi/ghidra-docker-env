# -*- coding: utf-8 -*-
"""PyGhidra runtime entry helpers."""

import sys
import tempfile
from pathlib import Path

from .._pyghidra_support import load_pyghidra
from ...config import GHIDRA_INSTALL_DIR
from ..commands.analyze import analyze_and_output, get_target_functions, list_all_functions
from ..commands.equivalence import run_equivalence_check


def run_pyghidra_mode(args):
    """PyGhidra モードで実行する。"""
    pyghidra = load_pyghidra()

    if args.equiv:
        run_equivalence_check(args)
        return

    target_path = args.target
    if not target_path:
        print("Error: バイナリファイルパスを指定してください")
        sys.exit(1)

    target_functions = get_target_functions(args)
    output_file = args.output
    quiet = args.quiet
    output_format = args.format
    debug = args.debug

    if args.hex:
        const_format = "hex"
    else:
        const_format = args.const_format

    if not quiet:
        print(f"Ghidraを起動: {GHIDRA_INSTALL_DIR}")
        print(f"解析対象: {target_path}")
        print(f"対象関数: {', '.join(target_functions)}")
        print(f"出力形式: {output_format}")
        print(f"定数形式: {const_format}")
        print()

    pyghidra.start(install_dir=Path(GHIDRA_INSTALL_DIR) if GHIDRA_INSTALL_DIR else None)

    with tempfile.TemporaryDirectory() as temp_dir:
        with pyghidra.open_project(temp_dir, "AnalysisProject", create=True) as project:
            loader = pyghidra.program_loader().project(project).source(target_path)
            with loader.load() as result:
                current_program = result.getPrimaryDomainObject()
                program_name = current_program.getName() or "UnknownProgram"
                pyghidra.analyze(current_program)

                if args.list_functions:
                    list_all_functions(current_program, output_file, quiet)
                    return

                analyze_and_output(
                    current_program,
                    target_functions,
                    output_format,
                    output_file,
                    quiet,
                    args.timeout,
                    debug,
                    program_name=program_name,
                    const_format=const_format,
                )
