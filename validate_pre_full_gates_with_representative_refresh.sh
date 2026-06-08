#!/usr/bin/env bash
# Refresh the small pre-full representative logs, then run the log-only gates.
#
# Use this before the expensive full rerun when recent producer/schema changes can
# make existing representative logs stale.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

export PARALLEL_JOBS="${PARALLEL_JOBS:-32}"

echo "Pre-full representative refresh:"
echo "  - Phase 2 equivalence_blocking_unsafety reduced pre-producer matrix"
echo "  - Phase 3 lane representative pairs"
echo "  - Log-only pre-full gates"
echo "Parallel jobs: $PARALLEL_JOBS"

./phase2_run_function_call_pre_producer_gate_reduced_matrix.sh
./phase2_validate_equivalence_blocking_unsafety_reduced_log_gate.sh

./phase3_run_function_call_return_coverage_lane1_representatives.sh
./phase3_run_function_call_return_width_bridge_lane2_representatives.sh
./phase3_run_loop_readonly_identity_lane3_representatives.sh
./phase3_run_loop_method_b_closure_lane4_representatives.sh
./phase3_run_function_call_sat_unsafety_lane5_representatives.sh
./phase3_run_function_call_unresolved_expression_lane6_representatives.sh
./phase3_run_loop_solver_rewrite_lane7_representatives.sh
./phase3_run_function_call_solver_rewrite_proof_lane8_representatives.sh
./phase3_run_function_call_solver_timeout_lane9_representatives.sh

./validate_log_only_pre_full_gates.sh

echo ""
echo "Pre-full representative refresh and validation finished."
