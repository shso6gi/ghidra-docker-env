#!/usr/bin/env bash
# NeqBench の全件評価（FULL_NEQ）の入口。start / status / stop / summary（eval/wrapper.py）。
#   eval/neq.sh start --freeze <commit>    eval/neq.sh status [--verify]
#   eval/neq.sh stop                       eval/neq.sh summary [--json]
set -euo pipefail
exec python3 -B "$(cd "$(dirname "$0")" && pwd)/wrapper.py" --matrix neq "$@"
