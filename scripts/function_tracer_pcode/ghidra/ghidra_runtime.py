# -*- coding: utf-8 -*-
"""Ghidra-script runtime entry helpers."""

from argparse import Namespace

from scripts.function_tracer_pcode.config import OUTPUT_FILE, OUTPUT_FORMAT
from scripts.function_tracer_pcode.cli.commands.analyze import (
    analyze_and_output,
    get_target_functions,
    list_all_functions,
)


def run_ghidra_mode(args=None):
    """Ghidra スクリプトモードで実行する。"""
    current_program = getCurrentProgram()  # type: ignore[name-defined]

    if args is None:
        args = Namespace(
            functions=None,
            format=OUTPUT_FORMAT,
            output=OUTPUT_FILE,
            quiet=False,
            list_functions=False,
            timeout=60,
            debug=False,
            hex=False,
            const_format="dec",
            equiv=None,
        )

    target_functions = get_target_functions(args)
    output_file = args.output
    quiet = args.quiet
    output_format = args.format

    if hasattr(args, "hex") and args.hex:
        const_format = "hex"
    elif hasattr(args, "const_format"):
        const_format = args.const_format
    else:
        const_format = "dec"

    program_name = current_program.getName() or "UnknownProgram"

    if not quiet:
        print(f"Program: {program_name}")
        print(f"対象関数: {', '.join(target_functions)}")
        print(f"出力形式: {output_format}")
        print(f"定数形式: {const_format}")
        print()

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
        debug=args.debug if hasattr(args, "debug") else False,
        program_name=program_name,
        const_format=const_format,
    )
