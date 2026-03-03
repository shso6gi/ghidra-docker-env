# -*- coding: utf-8 -*-
#!/usr/bin/env python3
#@category Analysis
#@author ReturnTracer
#@runtime PyGhidra
"""Return Tracer - Ghidra High P-code Return Value Analyzer"""

import sys
import argparse
import tempfile
from typing import List, Optional
from pathlib import Path

from ..config import (
    IN_GHIDRA,
    GHIDRA_INSTALL_DIR,
    TARGET_FUNCTIONS,
    OUTPUT_FILE,
    OUTPUT_FORMAT,
)
from ..analysis import ReturnAnalyzer
from ..io import OutputFormatter, output_result, write_to_file


def parse_arguments():
    """コマンドライン引数を解析"""
    parser = argparse.ArgumentParser(
        description="Ghidra High P-code Return Value Analyzer",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
使用例:
  # デフォルト設定で実行
  python3 -m scripts.function_tracer_pcode.main /workspace/targets/
  
  # 特定の関数を指定
  python3 -m scripts.function_tracer_pcode.main /workspace/targets/ -f main func1
  
  # 16進数表示で出力
  python3 -m scripts.function_tracer_pcode.main /workspace/targets/ --hex
  
  # SMT形式で出力
  python3 -m scripts.function_tracer_pcode.main /workspace/targets/ --format smt
  
  # 詳細形式で出力
  python3 -m scripts.function_tracer_pcode.main /workspace/targets/ --format detailed
  
  # ファイルに出力
  python3 -m scripts.function_tracer_pcode.main /workspace/targets/ -o output.txt
  
  # 等価性判定モード
  # 同じ関数名で比較
  python3 -m scripts.function_tracer_pcode.main --equiv binary1 binary2 -f target_function

  # 異なる関数名で比較
  python3 -m scripts.function_tracer_pcode.main --equiv binary1 binary2 -f func_in_bin1 func_in_bin2

  # タイムアウトを5分に設定
  python3 -m scripts.function_tracer_pcode.main --equiv binary1 binary2 -f func --equiv-timeout 300

  # 型修正リトライを有効にして比較（longlong/undefined → int）
  python3 -m scripts.function_tracer_pcode.main --equiv binary1 binary2 -f func --retry-with-int

  # デバッグモードで詳細を確認
  python3 -m scripts.function_tracer_pcode.main --equiv binary1 binary2 -f target_func --retry-with-int -d -v

  # 詳細出力とSMT式保存
  python3 -m scripts.function_tracer_pcode.main --equiv binary1 binary2 -f func -v --save-formula

  # デバッグモード
  python3 -m scripts.function_tracer_pcode.main --equiv binary1 binary2 -f func -d

  # リライトを無効にして実行
  python3 -m scripts.function_tracer_pcode.main --equiv binary1 binary2 -f modulo --no-rewrite
        """
    )
    
    parser.add_argument(
        "target",
        nargs="?",
        default=None,
        help="解析対象のバイナリファイルパス"
    )
    
    # === 等価性判定モード用引数 ===
    parser.add_argument(
        "--equiv",
        nargs=2,
        metavar=("BINARY1", "BINARY2"),
        default=None,
        help="等価性判定モード: 2つのバイナリを指定"
    )
    
    parser.add_argument(
        "--equiv-timeout",
        type=int,
        default=10,
        help="等価性判定のタイムアウト（秒）デフォルト: 10秒"
    )
    
    parser.add_argument(
        "--save-formula",
        action="store_true",
        help="生成されたSMT式を出力に含める"
    )
    
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="詳細な出力を表示"
    )
    
    parser.add_argument(
        "--functions", "-f",
        nargs="+",
        default=None,
        help="解析対象の関数名（複数可）。等価性判定時は1つまたは2つ指定"
    )
    
    parser.add_argument(
        "--format",
        choices=["text", "json", "smt", "detailed"],
        default=OUTPUT_FORMAT,
        help="出力形式を指定"
    )
    
    parser.add_argument(
        "--output", "-o",
        default=None,
        help="出力ファイルパス"
    )
    
    parser.add_argument(
        "--quiet", "-q",
        action="store_true",
        help="標準出力を抑制（ファイル出力のみ）"
    )
    
    parser.add_argument(
        "--list-functions",
        action="store_true",
        help="バイナリ内の全関数を一覧表示"
    )
    
    parser.add_argument(
        "--timeout",
        type=int,
        default=60,
        help="デコンパイルのタイムアウト（秒）"
    )

    parser.add_argument(
        "--debug", "-d",
        action="store_true",
        help="デバッグ出力を有効にする"
    )
    
    # 定数表示形式オプション
    parser.add_argument(
        "--hex",
        action="store_true",
        help="定数を16進数で表示"
    )
    
    parser.add_argument(
        "--const-format",
        choices=["dec", "hex", "auto"],
        default="dec",
        help="定数の表示形式 (dec: 10進数, hex: 16進数, auto: 自動判定)"
    )

    # === 型修正リトライオプション ===
    parser.add_argument(
        "--retry-with-int",
        action="store_true",
        help="等価性判定に失敗した場合、longlong/undefined型をint型に変更してリトライする"
    )
    
    parser.add_argument(
        "--no-rewrite",
        action="store_true",
        help="式のリライトを無効にする（デフォルト: 有効）"
    )

    parser.add_argument(
        "--rewrite-direction",
        choices=["to_modulo", "to_expansion"],
        default="to_modulo",
        help="リライト方向 (to_modulo: 展開形式→剰余演算子, to_expansion: 剰余演算子→展開形式)"
    )

    parser.add_argument(
        "--strategy",
        choices=["monolithic", "pairwise"],
        default="pairwise",
        help="等価性判定戦略 (monolithic: 単一の大きなite式, pairwise: 分岐ペア分割) デフォルト: pairwise"
    )

    return parser.parse_args()


def get_target_functions(args) -> List[str]:
    """解析対象の関数名リストを取得"""
    if args and hasattr(args, "functions") and args.functions:
        return args.functions
    return TARGET_FUNCTIONS


def list_all_functions(program, output_file: Optional[str] = None, quiet: bool = False):
    """バイナリ内の全関数を一覧表示"""
    function_manager = program.getFunctionManager()
    functions = function_manager.getFunctions(True)
    
    func_list = []
    for func in functions:
        func_list.append({
            "name": func.getName(),
            "entry_point": str(func.getEntryPoint()),
            "size": func.getBody().getNumAddresses()
        })
    
    lines = []
    lines.append("\n=== 関数一覧 ===")
    lines.append(f"{'Name':<40} {'Entry Point':<20} {'Size':>10}")
    lines.append("-" * 70)
    for f in func_list:
        lines.append(f"{f['name']:<40} {f['entry_point']:<20} {f['size']:>10}")
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
    const_format: str = "dec"
):
    """関数を解析して結果を出力"""
    from ..model import Expression
    
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
            analysis = analyzer.analyze_function_by_name(func_name, timeout)
            
            if analysis:
                content = OutputFormatter.format(analysis, output_format)
                output_result(content, output_file, quiet)
                processed_count += 1
            else:
                msg = f"[Warning] Function '{func_name}' not found or analysis failed"
                output_result(msg, output_file, quiet)
        
        completion_msg = f"\n"
        output_result(completion_msg, output_file, quiet)
        
    finally:
        analyzer.dispose()


def run_equivalence_check(args):
    """等価性判定を実行"""
    import pyghidra
    from ..equivalence import EquivalenceChecker, TypeFixerConfig
    
    binary1_path, binary2_path = args.equiv
    function_names = get_target_functions(args)
    
    # 関数名の処理
    if len(function_names) == 0:
        print("Error: 関数名を指定してください（-f オプション）")
        sys.exit(1)
    elif len(function_names) == 1:
        func_name1 = func_name2 = function_names[0]
    else:
        func_name1 = function_names[0]
        func_name2 = function_names[1]
    
    # 型修正リトライオプションを取得
    retry_with_type_fix = getattr(args, 'retry_with_int', False)

    # 戦略設定を取得（表示用）
    strategy = getattr(args, 'strategy', 'pairwise')
    
    if not args.quiet:
        print(f"等価性判定モード")
        print(f"  Binary 1: {binary1_path}")
        print(f"  Binary 2: {binary2_path}")
        print(f"  Function 1: {func_name1}")
        print(f"  Function 2: {func_name2}")
        print(f"  Strategy: {strategy}")
        print(f"  Timeout: {args.equiv_timeout}秒")
        print(f"  Retry with int type fix: {'enabled' if retry_with_type_fix else 'disabled'}")
        print()
    
    # Ghidra起動
    pyghidra.start(install_dir=Path(GHIDRA_INSTALL_DIR) if GHIDRA_INSTALL_DIR else None)
    
    # 型修正の設定（将来的に引数で制御可能にする場合はここを拡張）
    type_fixer_config = TypeFixerConfig()

    # リライト設定を取得
    enable_rewrite = not getattr(args, 'no_rewrite', False)
    rewrite_direction = getattr(args, 'rewrite_direction', 'to_modulo')
    
    # 戦略設定を取得
    strategy = getattr(args, 'strategy', 'pairwise')
    
    # 等価性チェッカーを初期化
    checker = EquivalenceChecker(
        timeout=args.equiv_timeout,
        debug=args.debug,
        type_fixer_config=type_fixer_config,
        enable_rewrite=enable_rewrite,
        rewrite_direction=rewrite_direction,
        strategy=strategy
    )
    
    # 利用可能なソルバーを表示
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
    
    # バイナリを開いて解析
    # 一時ディレクトリを作成してプロジェクトを管理
    with tempfile.TemporaryDirectory() as temp_dir:
        # プロジェクトを作成/オープン
        with pyghidra.open_project(temp_dir, "EquivCheckProject", create=True) as project:
            
            # Binary 1 をロード
            loader1 = pyghidra.program_loader().project(project).source(binary1_path).name("binary1")
            with loader1.load() as result1:
                program1 = result1.getPrimaryDomainObject()
                
                # 自動解析を実行 (open_programは自動で行っていたため明示的に呼び出し)
                pyghidra.analyze(program1)
                
                # Binary 2 をロード
                loader2 = pyghidra.program_loader().project(project).source(binary2_path).name("binary2")
                with loader2.load() as result2:
                    program2 = result2.getPrimaryDomainObject()
                    pyghidra.analyze(program2)
                    
                    # 等価性判定を実行（リトライオプションを渡す）
                    result = checker.check_from_binaries(
                        program1,
                        program2,
                        func_name1,
                        func_name2,
                        decompile_timeout=args.timeout,
                        save_formula=args.save_formula,
                        retry_with_type_fix=retry_with_type_fix
                    )
    
    # 結果を出力
    output_content = result.to_string(verbose=args.verbose)
    output_result(output_content, args.output, args.quiet)
    
    # SMT式を出力（オプション）
    if args.save_formula and result.smt_formula:
        if not args.quiet:
            print("\nGenerated SMT Formula:")
            print("-" * 70)
            print(result.smt_formula)
            print("-" * 70)
        
        if args.output:
            smt_output = args.output.rsplit('.', 1)[0] + '.smt2'
            with open(smt_output, 'w') as f:
                f.write(result.smt_formula)
            print(f"SMT formula saved to: {smt_output}")
    
    # 終了コード
    if result.is_equivalent is True:
        sys.exit(0)  # 等価
    elif result.is_equivalent is False:
        sys.exit(1)  # 非等価
    else:
        sys.exit(2)  # 不明


def run_ghidra_mode(args=None):
    """Ghidraスクリプトモードで実行"""
    from ..model import Expression
    
    current_program = getCurrentProgram()  # type: ignore[name-defined]
    
    if args is None:
        # デフォルト設定を使用
        class DefaultArgs:
            functions = None
            format = OUTPUT_FORMAT
            output = OUTPUT_FILE
            quiet = False
            list_functions = False
            timeout = 60
            debug = False
            hex = False
            const_format = "dec"
            equiv = None
        args = DefaultArgs()
    
    target_functions = get_target_functions(args)
    output_file = args.output
    quiet = args.quiet
    output_format = args.format
    
    if hasattr(args, 'hex') and args.hex:
        const_format = "hex"
    elif hasattr(args, 'const_format'):
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
        debug=args.debug if hasattr(args, 'debug') else False,
        program_name=program_name,
        const_format=const_format
    )


def run_pyghidra_mode(args):
    """PyGhidraモードで実行"""
    import pyghidra
    from ..model import Expression
    
    # 等価性判定モードの場合
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
            
            # バイナリをロード
            loader = pyghidra.program_loader().project(project).source(target_path)
            
            with loader.load() as result:
                current_program = result.getPrimaryDomainObject()
                
                program_name = current_program.getName() or "UnknownProgram"
                
                # 自動解析を実行
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
                    const_format=const_format
                )


def main():
    """メインエントリーポイント"""
    if IN_GHIDRA:
        run_ghidra_mode()
    else:
        args = parse_arguments()
        run_pyghidra_mode(args)


if __name__ == "__main__":
    main()