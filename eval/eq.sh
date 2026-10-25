#!/usr/bin/env bash
# EqBench の全件評価（FULL_EQBENCH）の入口。start / status / stop / summary（eval/wrapper.py）。
#   eval/eq.sh start --freeze <commit>    eval/eq.sh status [--verify]
#   eval/eq.sh stop                       eval/eq.sh summary [--json]
set -euo pipefail
exec python3 -B "$(cd "$(dirname "$0")" && pwd)/wrapper.py" --matrix eq "$@"
