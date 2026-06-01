#!/usr/bin/env bash
# Focused Phase 2 final-result movement preflight.
#
# This is a shell-level safety check, not the Phase 2 expected-movement
# validator. It runs the producer flags on the known return-coverage sentinel
# pair and requires the filtered baseline final result to stay unchanged.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

export OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_pre_producer_final_result_preflight}"
export FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_recursive_sum}"
export FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-fc_recursive_sum:B3_B7}"
export PARALLEL_JOBS="${PARALLEL_JOBS:-1}"
export VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-0}"
export VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-1}"
export VALIDATION_BASELINE_MATCH_SCOPE="${VALIDATION_BASELINE_MATCH_SCOPE:-after-pairs}"
export VALIDATION_BASELINE_MATCH_LEVEL="${VALIDATION_BASELINE_MATCH_LEVEL:-final-results}"
export PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-0}"
export PHASE2_RUN_KIND="${PHASE2_RUN_KIND:-phase2_function_call_pre_producer_final_result_preflight}"
export PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT="${PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT:-none}"
export PHASE2_EXPECTED_REASON_MOVEMENT="${PHASE2_EXPECTED_REASON_MOVEMENT:-preflight-final-result-invariant}"

exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_pre_producer_32jobs.sh"
