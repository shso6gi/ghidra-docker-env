# -*- coding: utf-8 -*-
"""runner の具体実行の設定（段と予算）の解決（Issue #323, C4）。

runner（Eq / Neq の matrix、固定 subset）が pair へ渡す具体実行の設定を **1 箇所で** 解決する。
規則はここにだけあり、shell 側は `validation_resolve_concrete_policy`
（`scripts/validation_matrix_common.sh`）からこの module を呼ぶだけにする。

============================ =========================================================================
入力                         規則
============================ =========================================================================
`EQBENCH_CONCRETE_STAGES`    段の集合。``witness_replay``（SAT witness の再生、#18 C2）を ``,`` で並べる。
                             ``none`` で無効。未指定・空は既定（``witness_replay`` = CLI の既定と同じ）。
                             段の名前の表は `checker.concrete_replay.CONCRETE_STAGES`（C5 はそこへ足す）
`EQBENCH_CONCRETE_BUDGET`    1 pair の具体実行の予算（秒、正）。未指定・空は既定（CLI の既定 60）
解析の期限                   `runner_timeout_policy` が解決した `analysis_timeout_enabled`
============================ =========================================================================

* 具体実行は解析の期限の中でだけ走る（`authority.decision.conditional_lane._concrete_lane_budget`）。
  期限が無いとき、段を **明示的に** 要求していれば `ConcretePolicyError`（runner は pair を始めずに
  exit 1）。既定のままなら有効な段は無し（``no_analysis_deadline``）として記録し、警告を出す。
* 記録と identity は **実際に有効な** 値で作る。有効な段が無ければ CLI には無効の flag を渡し、
  予算は ``0`` と記録する（期限なしの要求 on は off と同じ計算なので、同じ identity になる）。
* 値の書式（秒）は `runner_timeout_policy.parse_seconds` と同じ規則（CLI と共有）。

記録（`manifest_fields`）: run manifest / subset manifest へ書く key の唯一の一覧。
`concrete_stages` と `concrete_budget` は解析の設定の identity（`execution_receipt` の
analysis config v6）にも入る。
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from decimal import Decimal
from typing import Dict, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.checker.concrete_replay import (
    CONCRETE_STAGES,
    INACTIVE_NO_ANALYSIS_DEADLINE,
    INACTIVE_NOT_REQUESTED,
    STAGE_WITNESS_REPLAY,
)
from scripts.function_tracer_pcode.reporting.runner_timeout_policy import (
    TimeoutPolicyError,
    parse_seconds,
    seconds_text,
)

STAGES_VARIABLE = "EQBENCH_CONCRETE_STAGES"
BUDGET_VARIABLE = "EQBENCH_CONCRETE_BUDGET"

#: 段なしの綴り（空文字列は「未指定」なので、無効は明示的にこう書く）
NO_STAGES = "none"
#: 既定（CLI の既定と同じ: SAT witness の再生が有効、予算 60 秒）
DEFAULT_STAGES = STAGE_WITNESS_REPLAY
DEFAULT_BUDGET = "60"
#: 有効な段が無いときに記録する予算
NO_BUDGET = "0"

#: run manifest の key。並びは manifest に書く順。
KEY_STAGES_REQUESTED = "concrete_stages_requested"
KEY_BUDGET_REQUESTED = "concrete_budget_requested"
KEY_STAGES = "concrete_stages"
KEY_BUDGET = "concrete_budget"
KEY_INACTIVE_REASON = "concrete_inactive_reason"
MANIFEST_KEYS: Tuple[str, ...] = (
    KEY_STAGES_REQUESTED,
    KEY_BUDGET_REQUESTED,
    KEY_STAGES,
    KEY_BUDGET,
    KEY_INACTIVE_REASON,
)
#: 有効な段があるときの ``concrete_inactive_reason``
ACTIVE = "active"

#: 段ごとの CLI の flag（有効なとき / 無効のとき）。段を足すときはここにも足す。
_WITNESS_REPLAY_BUDGET_FLAG = "--concrete-replay-budget"
_WITNESS_REPLAY_OFF_FLAG = "--no-concrete-replay"


class ConcretePolicyError(ValueError):
    """runner の具体実行の設定が不正・不整合（runner は pair を始めずに exit 1 する）。"""


def parse_stages(raw: str) -> Tuple[str, ...]:
    """``witness_replay`` / ``none`` / ``a,b`` を、登録表の順の段の組にする。

    空白・空の要素・重複・未知の段・``none`` と段の混在は拒む（綴りを推測しない）。
    """

    if raw == NO_STAGES:
        return ()
    names = raw.split(",")
    unknown = [name for name in names if name not in CONCRETE_STAGES]
    if not raw or unknown:
        raise ConcretePolicyError(
            f"{STAGES_VARIABLE} must be {NO_STAGES!r} or a comma-separated list of "
            f"{', '.join(CONCRETE_STAGES)}: {raw!r}"
        )
    if len(set(names)) != len(names):
        raise ConcretePolicyError(f"{STAGES_VARIABLE} names a stage twice: {raw!r}")
    return tuple(stage for stage in CONCRETE_STAGES if stage in names)


def stages_text(stages: Sequence[str]) -> str:
    """記録・identity の段の綴り（登録表の順、``,`` 区切り。空は ``none``）。"""

    return ",".join(stages) if stages else NO_STAGES


@dataclass(frozen=True)
class RunnerConcretePolicy:
    """解決済みの runner の具体実行の設定。"""

    requested_stages: Tuple[str, ...]
    requested_budget: Decimal
    stages: Tuple[str, ...]
    inactive_reason: Optional[str]

    @property
    def budget(self) -> Decimal:
        """有効な予算（有効な段が無ければ 0）。"""
        return self.requested_budget if self.stages else Decimal(0)

    def cli_args(self) -> Tuple[str, ...]:
        """pair の CLI へ足す引数（段ごとに、有効ならその設定、無効なら無効の flag）。"""

        args = []
        if STAGE_WITNESS_REPLAY in self.stages:
            args += [_WITNESS_REPLAY_BUDGET_FLAG, seconds_text(self.budget)]
        else:
            args.append(_WITNESS_REPLAY_OFF_FLAG)
        return tuple(args)

    def manifest_fields(self) -> Dict[str, str]:
        return {
            KEY_STAGES_REQUESTED: stages_text(self.requested_stages),
            KEY_BUDGET_REQUESTED: seconds_text(self.requested_budget),
            KEY_STAGES: stages_text(self.stages),
            KEY_BUDGET: seconds_text(self.budget) if self.stages else NO_BUDGET,
            KEY_INACTIVE_REASON: self.inactive_reason or ACTIVE,
        }


def resolve_runner_concrete_policy(
    *,
    stages: Optional[str],
    budget: Optional[str],
    analysis_timeout_enabled: bool,
) -> Tuple[RunnerConcretePolicy, Optional[str]]:
    """runner の具体実行の設定の **唯一の** 解決と検証。

    返り値は ``(設定, 警告)``。警告は既定の段が期限なしで無効になったときだけ（runner は
    stderr に出して続ける）。不正・不整合は `ConcretePolicyError`。
    """

    explicit = bool(stages)
    requested = parse_stages(stages if explicit else DEFAULT_STAGES)
    try:
        requested_budget = parse_seconds(budget or DEFAULT_BUDGET, variable=BUDGET_VARIABLE)
    except TimeoutPolicyError as exc:
        raise ConcretePolicyError(str(exc)) from exc
    warning = None
    if not requested:
        effective: Tuple[str, ...] = ()
        inactive: Optional[str] = INACTIVE_NOT_REQUESTED
    elif not analysis_timeout_enabled:
        if explicit:
            raise ConcretePolicyError(
                f"{STAGES_VARIABLE}={stages_text(requested)} needs the analysis deadline "
                f"(concrete execution runs only inside it), but ANALYSIS_TIMEOUT is 0. Set "
                f"ANALYSIS_TIMEOUT, or {STAGES_VARIABLE}={NO_STAGES}."
            )
        effective, inactive = (), INACTIVE_NO_ANALYSIS_DEADLINE
        warning = (
            f"Warning: ANALYSIS_TIMEOUT is 0, so the default concrete stages "
            f"({stages_text(requested)}) do not run; recorded as {KEY_STAGES}={NO_STAGES} "
            f"({INACTIVE_NO_ANALYSIS_DEADLINE})."
        )
    else:
        effective, inactive = requested, None
    policy = RunnerConcretePolicy(
        requested_stages=requested,
        requested_budget=requested_budget,
        stages=effective,
        inactive_reason=inactive,
    )
    return policy, warning


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = parser.add_subparsers(dest="command", required=True)
    resolve = commands.add_parser(
        "resolve",
        help="validate the concrete settings and print the effective values as key=value "
             "lines, then the CLI arguments as cli_arg=... lines",
    )
    resolve.add_argument("--stages", default="", help=f"raw {STAGES_VARIABLE} ('' = unset)")
    resolve.add_argument("--budget", default="", help=f"raw {BUDGET_VARIABLE} ('' = unset)")
    resolve.add_argument(
        "--analysis-timeout-enabled", required=True, choices=("0", "1"),
        help="the resolved analysis_timeout_enabled of runner_timeout_policy",
    )
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = _build_parser().parse_args(argv)
    try:
        policy, warning = resolve_runner_concrete_policy(
            stages=args.stages,
            budget=args.budget,
            analysis_timeout_enabled=args.analysis_timeout_enabled == "1",
        )
    except ConcretePolicyError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1
    if warning:
        print(warning, file=sys.stderr)
    for key, value in policy.manifest_fields().items():
        print(f"{key}={value}")
    for value in policy.cli_args():
        print(f"cli_arg={value}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
