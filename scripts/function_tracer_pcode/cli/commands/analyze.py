# -*- coding: utf-8 -*-
"""Analysis-mode CLI helpers."""

from typing import List, Optional

from scripts.function_tracer_pcode.analysis import ReturnAnalyzer
from scripts.function_tracer_pcode.config import TARGET_FUNCTIONS
from scripts.function_tracer_pcode.reporting import OutputFormatter, output_result


def get_target_functions(args) -> List[str]:
    """解析対象の関数名リストを取得する。"""
    if args and hasattr(args, "functions") and args.functions:
        return args.functions
    return TARGET_FUNCTIONS


def list_all_functions(program, output_file: Optional[str] = None, quiet: bool = False):
    """バイナリ内の全関数を一覧表示する。"""
    function_manager = program.getFunctionManager()
    functions = function_manager.getFunctions(True)

    func_list = []
    for func in functions:
        func_list.append(
            {
                "name": func.getName(),
                "entry_point": str(func.getEntryPoint()),
                "size": func.getBody().getNumAddresses(),
            }
        )

    lines = []
    lines.append("\n=== 関数一覧 ===")
    lines.append(f"{'Name':<40} {'Entry Point':<20} {'Size':>10}")
    lines.append("-" * 70)
    for func in func_list:
        lines.append(f"{func['name']:<40} {func['entry_point']:<20} {func['size']:>10}")
    lines.append(f"\nTotal: {len(func_list)} functions")

    content = "\n".join(lines)
    output_result(content, output_file, quiet)
    return func_list


def analyze_and_output(
    program,
    function_names: List[str],
    output_format: str = "text",
    output_file: Optional[str] = None,
    quiet: bool = False,
    timeout: int = 60,
    debug: bool = False,
    program_name: Optional[str] = None,
    const_format: str = "dec",
):
    """関数を解析して結果を出力する。"""
    from scripts.function_tracer_pcode.core import Expression
    from scripts.function_tracer_pcode.analysis.condition.condition_cache import (
        condition_cache_scope,
    )

    Expression.set_constant_format(const_format)

    if debug:
        print(f"[DEBUG] Constant format set to: {const_format}")

    analyzer = ReturnAnalyzer(program, debug=debug)

    try:
        if program_name:
            header = OutputFormatter.format_header(program_name, output_format)
            output_result(header, output_file, quiet)

        processed_count = 0
        for func_name in function_names:
            # Issue #105 PR-105-A: 条件簡約の cache は解析 1 単位（関数 1 つ）の寿命
            with condition_cache_scope():
                analysis = analyzer.analyze_function_by_name(func_name, timeout)
            if analysis:
                content = OutputFormatter.format(analysis, output_format)
                output_result(content, output_file, quiet)
                processed_count += 1
            else:
                msg = f"[Warning] Function '{func_name}' not found or analysis failed"
                output_result(msg, output_file, quiet)

        completion_msg = f"\n解析完了: {processed_count}/{len(function_names)} 関数"
        output_result(completion_msg, output_file, quiet)
    finally:
        analyzer.dispose()
