#!/usr/bin/env bash
# Run log-only gates that can fail before a full 32-job rerun is needed.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "Log-only pre-full validation gates:"
echo "  - Phase 0 observed-baseline integrity/census/audit gates"
echo "  - Phase 3 post-fix gates rebuilt from existing representative logs"

./phase0_validate_observed_baseline_gates.sh
./phase3_rebuild_all_post_fix_gates_from_logs.sh

echo ""
echo "Log-only pre-full validation gates finished."
