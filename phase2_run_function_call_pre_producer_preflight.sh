#!/usr/bin/env bash
# Fast Phase 2 producer preflight.
#
# This runs a small set of representative pairs with the same producer flags as
# the full pre-producer matrix. It is intended to catch final-result movement
# before spending hours on the full 20-function matrix.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

export OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_pre_producer_preflight}"
export FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_select_simple,fc_widen_then_bias,fc_long_branch_dispatch,fc_guarded_call}"
export FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-fc_select_simple:B1_B10,fc_widen_then_bias:B1_B14,fc_long_branch_dispatch:B1_B10,fc_guarded_call:B5_B13}"
export PARALLEL_JOBS="${PARALLEL_JOBS:-5}"
export VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-0}"
export VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-1}"
export VALIDATION_BASELINE_MATCH_SCOPE="${VALIDATION_BASELINE_MATCH_SCOPE:-after-pairs}"
export PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-0}"
export PHASE2_RUN_KIND="${PHASE2_RUN_KIND:-phase2_function_call_pre_producer_preflight}"
export PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT="${PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT:-none}"
export PHASE2_EXPECTED_REASON_MOVEMENT="${PHASE2_EXPECTED_REASON_MOVEMENT:-preflight-final-result-invariant}"

exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_pre_producer_32jobs.sh"
