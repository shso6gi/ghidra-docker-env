#!/usr/bin/env bash
# Run log-only gates that can fail before a full 32-job rerun is needed.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "Log-only pre-full validation gates:"
echo "  - Phase 0 observed-baseline integrity/census/audit gates"
echo "  - Phase 1 concrete manifest gate"
echo "  - Phase 1.5 pre-semantic-fix regression gates"
echo "  - Phase 2 equivalence_blocking_unsafety reduced log gate"
echo "  - Phase 3 post-fix gates rebuilt from existing representative logs"

./phase0_validate_observed_baseline_gates.sh
./phase1_validate_concrete_manifest_gate.sh
./phase15_validate_regression_gates.sh
./phase2_validate_equivalence_blocking_unsafety_reduced_log_gate.sh
./phase3_rebuild_all_post_fix_gates_from_logs.sh

echo ""
echo "Log-only pre-full validation gates finished."
