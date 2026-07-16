# -*- coding: utf-8 -*-
"""CLI argument definitions."""

import argparse
from typing import Optional, Sequence

from ..config import OUTPUT_FORMAT


CLI_EPILOG = """
使用例:
  # デフォルト設定で実行
  python3 -m scripts.function_tracer_pcode.cli.main /workspace/targets/binary
  
  # 特定の関数を指定
  python3 -m scripts.function_tracer_pcode.cli.main /workspace/targets/binary -f main func1
  
  # 16進数表示で出力
  python3 -m scripts.function_tracer_pcode.cli.main /workspace/targets/binary --hex
  
  # SMT形式で出力
  python3 -m scripts.function_tracer_pcode.cli.main /workspace/targets/binary --format smt
  
  # 詳細形式で出力
  python3 -m scripts.function_tracer_pcode.cli.main /workspace/targets/binary --format detailed
  
  # ファイルに出力
  python3 -m scripts.function_tracer_pcode.cli.main /workspace/targets/binary -o output.txt
  
  # 等価性判定モード
  # 同じ関数名で比較（recovery phases デフォルト有効）
  python3 -m scripts.function_tracer_pcode.cli.main --equiv binary1 binary2 -f target_function

  # 異なる関数名で比較
  python3 -m scripts.function_tracer_pcode.cli.main --equiv binary1 binary2 -f func_in_bin1 func_in_bin2

  # タイムアウトを5分に設定
  python3 -m scripts.function_tracer_pcode.cli.main --equiv binary1 binary2 -f func --equiv-timeout 300

  # recovery phases を無効にして比較（型修正リトライなし）
  python3 -m scripts.function_tracer_pcode.cli.main --equiv binary1 binary2 -f func --no-retry-phases

  # Phase 2 producer 用: completed recovery proof による EQ 化を無効化
  python3 -m scripts.function_tracer_pcode.cli.main --equiv binary1 binary2 -f func --no-completed-recovery-proofs

  # デバッグモードで詳細を確認
  python3 -m scripts.function_tracer_pcode.cli.main --equiv binary1 binary2 -f target_func -d -v

  # 詳細出力とSMT式保存
  python3 -m scripts.function_tracer_pcode.cli.main --equiv binary1 binary2 -f func -v --save-formula

  # リライトを無効にして実行
  python3 -m scripts.function_tracer_pcode.cli.main --equiv binary1 binary2 -f modulo --no-rewrite

  # 正規化を安全な bit-vector 恒等式のみに制限
  python3 -m scripts.function_tracer_pcode.cli.main --equiv binary1 binary2 -f func --normalize-mode safe

  # facts 依存の正規化や template abstraction を明示的に有効化
  python3 -m scripts.function_tracer_pcode.cli.main --equiv binary1 binary2 -f func --normalize-mode full --enable-fact-normalization --enable-template-abstraction
"""


def build_parser() -> argparse.ArgumentParser:
    """CLI parser を構築する。"""
    parser = argparse.ArgumentParser(
        description="Ghidra High P-code Return Value Analyzer",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=CLI_EPILOG,
    )

    parser.add_argument(
        "target",
        nargs="?",
        default=None,
        help="解析対象のバイナリファイルパス",
    )

    parser.add_argument(
        "--equiv",
        nargs=2,
        metavar=("BINARY1", "BINARY2"),
        default=None,
        help="等価性判定モード: 2つのバイナリを指定",
    )
    parser.add_argument(
        "--binary-ids",
        nargs=2,
        metavar=("BINARY1_ID", "BINARY2_ID"),
        default=None,
        help="等価性判定の canonical binary ID（例: B10 B11）",
    )
    parser.add_argument(
        "--equiv-timeout",
        type=int,
        default=10,
        help="等価性判定のタイムアウト（秒）デフォルト: 10秒",
    )
    parser.add_argument(
        "--save-formula",
        action="store_true",
        help="生成されたSMT式を出力に含める",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="詳細な出力を表示",
    )
    parser.add_argument(
        "--functions",
        "-f",
        nargs="+",
        default=None,
        help="解析対象の関数名（複数可）。等価性判定時は1つまたは2つ指定",
    )
    parser.add_argument(
        "--format",
        choices=["text", "json", "smt", "detailed"],
        default=OUTPUT_FORMAT,
        help="出力形式を指定",
    )
    parser.add_argument(
        "--output",
        "-o",
        default=None,
        help="出力ファイルパス",
    )
    parser.add_argument(
        "--emit-result-json",
        action="store_true",
        help="等価性判定結果の機械可読JSONをログへ追記する",
    )
    parser.add_argument(
        "--quiet",
        "-q",
        action="store_true",
        help="標準出力を抑制（ファイル出力のみ）",
    )
    parser.add_argument(
        "--list-functions",
        action="store_true",
        help="バイナリ内の全関数を一覧表示",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=60,
        help="デコンパイルのタイムアウト（秒）",
    )
    parser.add_argument(
        "--debug",
        "-d",
        action="store_true",
        help="デバッグ出力を有効にする",
    )
    parser.add_argument(
        "--hex",
        action="store_true",
        help="定数を16進数で表示",
    )
    parser.add_argument(
        "--const-format",
        choices=["dec", "hex", "auto"],
        default="dec",
        help="定数の表示形式 (dec: 10進数, hex: 16進数, auto: 自動判定)",
    )
    parser.add_argument(
        "--no-retry-phases",
        action="store_true",
        help="Recovery phases（型修正リトライなど）を無効にする（デフォルト: 有効）",
    )
    parser.add_argument(
        "--no-completed-recovery-proofs",
        action="store_true",
        help="completed recovery proof を結果へ反映しない（Phase 2 producer 検証用）",
    )
    parser.add_argument(
        "--assume-fp-non-nan",
        action="store_true",
        help=(
            "float/double引数がNaNでない前提で等価性を判定する（明示前提つきEQ用）。"
            " 現状は32bit/64bit浮動小数点引数にのみ適用されます（例: long doubleなどは対象外）。"
        ),
    )
    parser.add_argument(
        "--observe-errno",
        action="store_true",
        help="errno の変更を観測対象に含める（pure libm call abstraction は無効化されます）",
    )
    parser.add_argument(
        "--observe-fenv",
        action="store_true",
        help="floating-point environment の変更を観測対象に含める（pure libm call abstraction は無効化されます）",
    )
    parser.add_argument(
        "--no-rewrite",
        action="store_true",
        help="式のリライトを無効にする（デフォルト: 有効）",
    )
    parser.add_argument(
        "--rewrite-direction",
        choices=["to_modulo", "to_expansion"],
        default="to_modulo",
        help="リライト方向 (to_modulo: 展開形式→剰余演算子, to_expansion: 剰余演算子→展開形式)",
    )
    parser.add_argument(
        "--strategy",
        choices=["monolithic", "pairwise"],
        default="pairwise",
        help="等価性判定戦略 (monolithic: 単一の大きなite式, pairwise: 分岐ペア分割) デフォルト: pairwise",
    )
    parser.add_argument(
        "--pairwise-timeout",
        type=int,
        default=5,
        help="Pairwise戦略の各クエリのタイムアウト（秒）デフォルト: 5",
    )
    parser.add_argument(
        "--pairwise-timeout-hard",
        type=int,
        default=30,
        help="Pairwise戦略の難しいクエリの再試行タイムアウト（秒）デフォルト: 30",
    )
    parser.add_argument(
        "--monolithic-timeout",
        type=int,
        default=None,
        help="Monolithic分割全体の専用タイムアウト（秒）。未指定時は--equiv-timeout",
    )
    parser.add_argument(
        "--monolithic-query-mode",
        choices=["split", "legacy"],
        default="split",
        help="Monolithic query encoding。split は region 分割、legacy は検証用の単一 query",
    )
    parser.add_argument(
        "--pairwise-save-unknown",
        action="store_true",
        help="Pairwise戦略でUNKNOWNになったクエリを/tmpに保存する",
    )
    parser.add_argument(
        "--pairwise-unknown-dir",
        default=None,
        help="--pairwise-save-unknown で保存する UNKNOWN クエリの出力ディレクトリ",
    )
    parser.add_argument(
        "--normalize-mode",
        choices=["off", "safe", "full"],
        default="safe",
        help="等価性判定内の normalize 方針 (off: 無効, safe: 明白な bit-vector 恒等式のみ, full: 追加の opt-in 正規化を許可)",
    )
    parser.add_argument(
        "--enable-fact-normalization",
        action="store_true",
        help="条件 facts に依存する normalize を有効にする（デフォルト: 無効）",
    )
    parser.add_argument(
        "--enable-template-abstraction",
        action="store_true",
        help="loop-template abstraction fallback を有効にする（デフォルト: 無効）",
    )
    return parser


def parse_arguments(argv: Optional[Sequence[str]] = None):
    """コマンドライン引数を解析する。"""
    return build_parser().parse_args(argv)
