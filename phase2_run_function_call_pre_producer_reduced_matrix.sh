#!/usr/bin/env bash
# Reduced Phase 2 producer matrix for fast investigation before the full 20-function run.
#
# This runs the functions that contributed to the latest Phase 2 producer
# canonical-baseline gate failure. It keeps the same producer flags as the full
# pre-producer matrix, but disables the Phase 2 representative movement gate
# because that gate expects the full representative set. The runner-level
# final-result baseline comparison remains enabled; reason/action movement is
# still reported in the summaries, but intentional producer proof metadata
# movement does not stop the reduced matrix.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

export OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_reduced_pre_producer}"
export FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_recursive_sum,fc_is_even,fc_is_odd,fc_read_after_void}"
export PARALLEL_JOBS="${PARALLEL_JOBS:-32}"
export VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-0}"
export VALIDATION_AUTO_BEFORE_SNAPSHOT="${VALIDATION_AUTO_BEFORE_SNAPSHOT:-0}"
export VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-1}"
export VALIDATION_BASELINE_MATCH_SCOPE="${VALIDATION_BASELINE_MATCH_SCOPE:-after-pairs}"
export VALIDATION_BASELINE_MATCH_LEVEL="${VALIDATION_BASELINE_MATCH_LEVEL:-final-results}"
export PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-0}"
export PHASE2_RUN_KIND="${PHASE2_RUN_KIND:-phase2_function_call_reduced_matrix_pre_producer}"
export PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT="${PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT:-none}"
export PHASE2_EXPECTED_REASON_MOVEMENT="${PHASE2_EXPECTED_REASON_MOVEMENT:-reduced-matrix-canonical-baseline-invariant}"

exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_pre_producer_32jobs.sh"
