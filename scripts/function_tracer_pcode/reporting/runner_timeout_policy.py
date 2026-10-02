# -*- coding: utf-8 -*-
"""runner の解析の期限（`ANALYSIS_TIMEOUT`）と pair process の期限の整合（Issue #106 PR-106-B）。

runner（Eq / Neq の matrix、固定 subset、CI）が pair へ渡す解析の期限を **1 箇所で** 解決し、
process の期限との整合を確かめる。規則はここにだけあり、shell 側は
`validation_resolve_analysis_timeout_policy`（`scripts/validation_matrix_common.sh`）からこの
module を呼ぶだけにする（Eq / Neq / full / subset / CI で規則を書き直さない）。

========================== =====================================================================
入力                       規則
========================== =====================================================================
`ANALYSIS_TIMEOUT`         秒（``480`` / ``480s`` / ``120.5``）。``0`` で期限なし（OFF、
                           `--analysis-timeout` を渡さない = PR-106-B 以前と同じ実行）。未指定・空は
                           runner の既定（full は `FULL_RUN_DEFAULT_ANALYSIS_TIMEOUT`、固定 subset は
                           `eqbench_subset.json` の `run_settings`）
`ANALYSIS_TIMEOUT_MARGIN`  正の秒。期限で打ち切った pair が確定処理・出力・後片付けを終えて
                           process の期限より前に終わるための余裕。未指定・空は
                           `DEFAULT_ANALYSIS_TIMEOUT_MARGIN`。OFF でも書式は検査し、記録する
`PAIR_PROCESS_TIMEOUT`     秒（runner の既存の書式）。**自動では設定も拡大もしない**
========================== =====================================================================

* 期限が有効なら ``ANALYSIS_TIMEOUT + ANALYSIS_TIMEOUT_MARGIN <= PAIR_PROCESS_TIMEOUT``（等号は可）。
  違反・不正な値は `TimeoutPolicyError` で、runner は pair を 1 つも始めずに exit 1 する
  （`DRY_RUN=1` でも同じ検査を通る）。
* 単位は秒だけ（末尾の ``s`` は省略可）。``m`` / ``h``・指数表記・符号・``inf`` / ``nan``・前後の空白・
  ``.5`` / ``5.`` は拒む。値は `Decimal` で比べる（2 進の丸めで境界の判定が揺れない）。
* 期限を pair へ渡す値（`cli_args`）は CLI の `--analysis-timeout`（正の有限な秒）が受け取れる
  形だけ。期限の意味（起点・checkpoint・打ち切り後の扱い）は `core/deadline.py` が持ち、ここでは
  決めない。

記録（`manifest_fields`）: 実効値を run manifest / subset manifest へ書く key の唯一の一覧。
`analysis_timeout` と `analysis_timeout_margin` は解析の設定の identity（`execution_receipt` の
analysis config v4）にも入り、publication manifest の `analysis_config` に残る。
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation
from typing import Dict, Optional, Sequence, Tuple

#: full matrix（Eq / Neq の runner）の既定の解析の期限（秒）= process の期限 600 s − 既定の余裕。
#: 固定 subset の既定は `eqbench_subset.json` の `run_settings.ANALYSIS_TIMEOUT`（240 s − 余裕）。
FULL_RUN_DEFAULT_ANALYSIS_TIMEOUT = "475"

#: 既定の余裕（秒）。根拠は PR-106-B の実測（`docs/profiling_timeout_pairs.md` の §10）: 区間ごとの
#: 観測最大の和 = 解析の外の固定費 + checkpoint の無い区間の越え + 打ち切り後の確定処理・出力 +
#: 後片付け（`reporting/deadline_margin_summary.py` が測る）+ supervisor の stack dump の先行時間を、
#: 5 s 単位に切り上げた値。観測した最大の和であって保証ではない（負荷・入力で越え得る。越えた
#: pair は supervisor の TIMEOUT になる）。
DEFAULT_ANALYSIS_TIMEOUT_MARGIN = "125"

ANALYSIS_TIMEOUT_VARIABLE = "ANALYSIS_TIMEOUT"
MARGIN_VARIABLE = "ANALYSIS_TIMEOUT_MARGIN"
PAIR_PROCESS_TIMEOUT_VARIABLE = "PAIR_PROCESS_TIMEOUT"

#: run manifest の key（実効値）。並びは manifest に書く順。
KEY_ANALYSIS_TIMEOUT = "analysis_timeout"
KEY_ANALYSIS_TIMEOUT_ENABLED = "analysis_timeout_enabled"
KEY_ANALYSIS_TIMEOUT_MARGIN = "analysis_timeout_margin"
MANIFEST_KEYS: Tuple[str, ...] = (
    KEY_ANALYSIS_TIMEOUT,
    KEY_ANALYSIS_TIMEOUT_ENABLED,
    KEY_ANALYSIS_TIMEOUT_MARGIN,
)

#: 期限なし（OFF）を表す値
OFF_SECONDS = Decimal(0)

CLI_FLAG = "--analysis-timeout"

_SECONDS = re.compile(r"(?P<number>[0-9]+(?:\.[0-9]+)?)s?")


class TimeoutPolicyError(ValueError):
    """runner の期限の設定が不正・不整合（runner は pair を始めずに exit 1 する）。"""


def parse_seconds(raw: str, *, variable: str) -> Decimal:
    """``480`` / ``480s`` / ``120.5`` を秒の `Decimal` にする（書式は module docstring）。"""

    match = _SECONDS.fullmatch(raw)
    if match is None:
        raise TimeoutPolicyError(
            f"{variable} must be a number of seconds such as 480 or 480s "
            f"(no other unit, sign or exponent): {raw!r}"
        )
    try:
        return Decimal(match.group("number"))
    except InvalidOperation as exc:  # pragma: no cover - the pattern admits only digits
        raise TimeoutPolicyError(f"{variable} is not a number of seconds: {raw!r}") from exc


def seconds_text(value: Decimal) -> str:
    """記録・CLI へ渡す秒の綴り（指数表記なし、末尾の 0 なし。``480.0`` → ``480``）。"""

    if value == value.to_integral_value():
        return str(value.quantize(Decimal(1)))
    return format(value.normalize(), "f")


@dataclass(frozen=True)
class RunnerTimeoutPolicy:
    """解決済みの runner の期限（実効値）。"""

    analysis_timeout: Decimal
    margin: Decimal
    pair_process_timeout: Decimal

    @property
    def enabled(self) -> bool:
        return self.analysis_timeout != OFF_SECONDS

    def cli_args(self) -> Tuple[str, ...]:
        """pair の CLI へ足す引数（OFF なら空 = PR-106-B 以前と同じ argv）。"""

        if not self.enabled:
            return ()
        return (CLI_FLAG, seconds_text(self.analysis_timeout))

    def manifest_fields(self) -> Dict[str, str]:
        return {
            KEY_ANALYSIS_TIMEOUT: seconds_text(self.analysis_timeout),
            KEY_ANALYSIS_TIMEOUT_ENABLED: "1" if self.enabled else "0",
            KEY_ANALYSIS_TIMEOUT_MARGIN: seconds_text(self.margin),
        }


def resolve_runner_timeout_policy(
    *,
    analysis_timeout: Optional[str],
    margin: Optional[str],
    pair_process_timeout: str,
    default_analysis_timeout: str = FULL_RUN_DEFAULT_ANALYSIS_TIMEOUT,
) -> RunnerTimeoutPolicy:
    """runner の期限の **唯一の** 解決と検証（未指定・空は既定。不整合は `TimeoutPolicyError`）。"""

    if analysis_timeout:
        timeout = parse_seconds(analysis_timeout, variable=ANALYSIS_TIMEOUT_VARIABLE)
        source = "set"
    else:
        timeout = parse_seconds(
            default_analysis_timeout, variable=f"default {ANALYSIS_TIMEOUT_VARIABLE}",
        )
        source = "runner default"
    margin_value = parse_seconds(
        margin or DEFAULT_ANALYSIS_TIMEOUT_MARGIN, variable=MARGIN_VARIABLE,
    )
    if margin_value <= 0:
        raise TimeoutPolicyError(
            f"{MARGIN_VARIABLE} must be a positive number of seconds: {margin!r}"
        )
    process = parse_seconds(pair_process_timeout, variable=PAIR_PROCESS_TIMEOUT_VARIABLE)
    policy = RunnerTimeoutPolicy(
        analysis_timeout=timeout,
        margin=margin_value,
        pair_process_timeout=process,
    )
    if policy.enabled and timeout + margin_value > process:
        raise TimeoutPolicyError(
            f"{ANALYSIS_TIMEOUT_VARIABLE} ({seconds_text(timeout)}s, {source}) + "
            f"{MARGIN_VARIABLE} ({seconds_text(margin_value)}s) = "
            f"{seconds_text(timeout + margin_value)}s exceeds "
            f"{PAIR_PROCESS_TIMEOUT_VARIABLE} ({seconds_text(process)}s). Lower "
            f"{ANALYSIS_TIMEOUT_VARIABLE}, or set it to 0 to run without the analysis "
            f"deadline; {PAIR_PROCESS_TIMEOUT_VARIABLE} is never raised automatically."
        )
    return policy


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = parser.add_subparsers(dest="command", required=True)
    resolve = commands.add_parser(
        "resolve",
        help="validate the runner settings and print the effective values as key=value lines",
    )
    resolve.add_argument("--analysis-timeout", default="", help="raw ANALYSIS_TIMEOUT ('' = unset)")
    resolve.add_argument(
        "--analysis-timeout-margin", default="", help="raw ANALYSIS_TIMEOUT_MARGIN ('' = unset)",
    )
    resolve.add_argument("--pair-process-timeout", required=True, help="raw PAIR_PROCESS_TIMEOUT")
    resolve.add_argument(
        "--default-analysis-timeout", default=FULL_RUN_DEFAULT_ANALYSIS_TIMEOUT,
        help="the default this runner applies when ANALYSIS_TIMEOUT is unset",
    )
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = _build_parser().parse_args(argv)
    try:
        policy = resolve_runner_timeout_policy(
            analysis_timeout=args.analysis_timeout,
            margin=args.analysis_timeout_margin,
            pair_process_timeout=args.pair_process_timeout,
            default_analysis_timeout=args.default_analysis_timeout,
        )
    except TimeoutPolicyError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1
    for key, value in policy.manifest_fields().items():
        print(f"{key}={value}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
