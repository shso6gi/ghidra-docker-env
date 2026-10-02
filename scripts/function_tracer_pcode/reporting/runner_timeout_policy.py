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
                           profile の既定（`profile_defaults`: full は `FULL_RUN_DEFAULT_ANALYSIS_TIMEOUT`、
                           固定 subset は `eqbench_subset.json` の `run_settings`）
`ANALYSIS_TIMEOUT_MARGIN`  正の秒。期限で打ち切った pair の child が、process の期限の lead window の
                           手前で終わるための余裕。未指定・空は profile の既定（full は
                           `DEFAULT_ANALYSIS_TIMEOUT_MARGIN`）。OFF でも書式は検査し、記録する
`PAIR_PROCESS_TIMEOUT`     秒（runner の既存の書式）。**自動では設定も拡大もしない**
========================== =====================================================================

* 期限が有効なら ``ANALYSIS_TIMEOUT + ANALYSIS_TIMEOUT_MARGIN <= PAIR_PROCESS_TIMEOUT``（等号は可）。
  違反・不正な値は `TimeoutPolicyError` で、runner は pair を 1 つも始めずに exit 1 する
  （`DRY_RUN=1` でも同じ検査を通る）。
* 単位は秒だけ（末尾の ``s`` は省略可）。``m`` / ``h``・指数表記・符号・``inf`` / ``nan``・前後の空白・
  ``.5`` / ``5.`` は拒む。
* 値は **消費者が読む値**: CLI（`--analysis-timeout`）も supervisor（`--timeout-seconds`）も
  ``float`` で読むので、正の有限な double でなければ拒む（規則は CLI と共有の
  `core.deadline.parse_budget_seconds`）。10 進では正でも double で 0 や ``inf`` になる綴りは
  pair を始める前に拒まれる。比較・記録・CLI へ渡す綴りは、その double の最短の 10 進表現
  （`Decimal`）で行い、2 進の丸めで境界の判定が揺れない。
* 期限の意味（起点・checkpoint・打ち切り後の扱い）は `core/deadline.py` が持ち、ここでは決めない。
  既定の margin の観測は `reporting/deadline_margin_summary.py`、計測集合・採用式・判定は
  `reporting/deadline_margin_acceptance.py`。

記録（`manifest_fields`）: 実効値を run manifest / subset manifest へ書く key の唯一の一覧。
`analysis_timeout` と `analysis_timeout_margin` は解析の設定の identity（`execution_receipt` の
analysis config v4）にも入り、publication manifest の `analysis_config` に残る。
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from decimal import Decimal
from pathlib import Path
from typing import Dict, Optional, Sequence, Tuple

#: full matrix（Eq / Neq の runner）の profile の既定の解析の期限（秒）= process の期限 600 s − 既定の
#: 余裕。固定 subset の profile は `eqbench_subset.json` の `run_settings`（240 s − その profile の余裕）。
FULL_RUN_DEFAULT_ANALYSIS_TIMEOUT = "410"

#: full matrix の profile の既定の余裕（秒）。`reporting/deadline_margin_acceptance.py` の採用式
#: （固定費・checkpoint の無い区間の越え・打ち切り後の確定処理と出力・後片付けの区間ごとの観測最大の和
#: + stack dump の lead、5 s 単位に切り上げ）を、`docs/profiling_timeout_pairs.md` §10 の run の一覧に
#: 当てた値。観測した最大の和であって保証ではない（越えた pair は supervisor の TIMEOUT になる）。
DEFAULT_ANALYSIS_TIMEOUT_MARGIN = "190"

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


def parse_seconds(raw: str, *, variable: str, allow_zero: bool = False) -> Decimal:
    """``480`` / ``480s`` / ``120.5`` を、実際に使われる秒の値にする（書式は module docstring）。

    綴りは 10 進だけ（符号・指数・単位なし）。値は **その綴りを消費者が読んだ値**: CLI も
    supervisor も ``float`` で読むので、`core.deadline.parse_budget_seconds`（CLI と共有の規則）が
    受け取る正の有限な double でなければ拒む。10 進では正でも double で 0 や ``inf`` になる綴り
    （``0.<400 個の 0>1``、``1<400 個の 0>``）はここで拒まれ、pair を 1 つも始めない。返す
    `Decimal` はその double の最短の 10 進表現なので、比較・記録・CLI へ渡す綴りがすべて同じ値を指す。
    ``allow_zero`` なら、10 進で 0 の綴りを OFF（``Decimal(0)``）として受け取る。
    """

    from scripts.function_tracer_pcode.core.deadline import parse_budget_seconds

    match = _SECONDS.fullmatch(raw)
    if match is None:
        raise TimeoutPolicyError(
            f"{variable} must be a number of seconds such as 480 or 480s "
            f"(no other unit, sign or exponent): {raw!r}"
        )
    number = match.group("number")
    if allow_zero and Decimal(number) == 0:
        return OFF_SECONDS
    try:
        effective = parse_budget_seconds(number)
    except ValueError as exc:
        raise TimeoutPolicyError(
            f"{variable} must be a positive number of seconds that the pair process can "
            f"represent (a finite, non-zero double): {raw!r}"
        ) from exc
    return Decimal(repr(effective))


def seconds_text(value: Decimal) -> str:
    """記録・CLI へ渡す秒の綴り（指数表記なし、末尾の 0 なし。``480.0`` → ``480``）。

    `parse_seconds` が返す値なら、``float(seconds_text(v))`` は消費者が読む double と一致する。
    """

    if value == value.to_integral_value():
        return format(value.to_integral_value(), "f")
    return format(value, "f")


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
    default_margin: str = DEFAULT_ANALYSIS_TIMEOUT_MARGIN,
) -> RunnerTimeoutPolicy:
    """runner の期限の **唯一の** 解決と検証（未指定・空は既定。不整合は `TimeoutPolicyError`）。"""

    if analysis_timeout:
        timeout = parse_seconds(
            analysis_timeout, variable=ANALYSIS_TIMEOUT_VARIABLE, allow_zero=True,
        )
        source = "set"
    else:
        timeout = parse_seconds(
            default_analysis_timeout, variable=f"default {ANALYSIS_TIMEOUT_VARIABLE}",
            allow_zero=True,
        )
        source = "runner default"
    margin_value = parse_seconds(margin or default_margin, variable=MARGIN_VARIABLE)
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


#: profile の既定値を持つ manifest（`eqbench_subset.json`）の key
PROFILE_SETTINGS_KEY = "run_settings"


def profile_defaults(manifest_path: Optional[Path]) -> Tuple[str, str]:
    """runner の profile の既定 ``(ANALYSIS_TIMEOUT, ANALYSIS_TIMEOUT_MARGIN)``。

    ``None`` は full matrix の profile（この module の定数）。manifest を渡したら、その
    ``run_settings`` の 2 つの値（固定 subset の profile）。どちらかが欠けていれば
    `TimeoutPolicyError`（full の既定へ黙って戻らない）。
    """

    if manifest_path is None:
        return FULL_RUN_DEFAULT_ANALYSIS_TIMEOUT, DEFAULT_ANALYSIS_TIMEOUT_MARGIN
    try:
        settings = json.loads(Path(manifest_path).read_text(encoding="utf-8"))[PROFILE_SETTINGS_KEY]
        values = (settings[ANALYSIS_TIMEOUT_VARIABLE], settings[MARGIN_VARIABLE])
    except (OSError, ValueError, KeyError, TypeError) as exc:
        raise TimeoutPolicyError(
            f"{manifest_path} names no {PROFILE_SETTINGS_KEY}.{ANALYSIS_TIMEOUT_VARIABLE} / "
            f"{MARGIN_VARIABLE}: {exc}"
        ) from exc
    if not all(isinstance(value, str) and value for value in values):
        raise TimeoutPolicyError(f"{manifest_path}: the profile defaults must be strings")
    return values


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
        "--profile-manifest", type=Path, default=None,
        help="take the defaults from this manifest's run_settings (the fixed subset); "
             "without it the full-run defaults apply",
    )
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = _build_parser().parse_args(argv)
    try:
        default_timeout, default_margin = profile_defaults(args.profile_manifest)
        policy = resolve_runner_timeout_policy(
            analysis_timeout=args.analysis_timeout,
            margin=args.analysis_timeout_margin,
            pair_process_timeout=args.pair_process_timeout,
            default_analysis_timeout=default_timeout,
            default_margin=default_margin,
        )
    except TimeoutPolicyError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1
    for key, value in policy.manifest_fields().items():
        print(f"{key}={value}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
