#!/usr/bin/env bash
# Reduced Phase 2 producer expected-movement gate.
#
# This runs the three Phase 2 representatives plus representative samples of
# the full-matrix baseline-gate contributor shapes. It keeps the producer flags
# and expected-movement validator enabled, but compares the baseline only for
# the pairs produced by this reduced run.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

export OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_gate_reduced_pre_producer}"
export FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_apply_indirect,fc_dispatch_indirect,fc_recursive_sum,fc_is_even,fc_is_odd}"
export FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-fc_apply_indirect:B10_B11,fc_dispatch_indirect:B10_B11,fc_recursive_sum:B10_B14,fc_apply_indirect:B1_B2,fc_apply_indirect:B1_B14,fc_is_even:B1_B10,fc_is_odd:B1_B10}"
export PARALLEL_JOBS="${PARALLEL_JOBS:-8}"
export VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-0}"
export VALIDATION_AUTO_BEFORE_SNAPSHOT="${VALIDATION_AUTO_BEFORE_SNAPSHOT:-0}"
export VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-1}"
export VALIDATION_BASELINE_MATCH_SCOPE="${VALIDATION_BASELINE_MATCH_SCOPE:-after-pairs}"
export VALIDATION_BASELINE_MATCH_LEVEL="${VALIDATION_BASELINE_MATCH_LEVEL:-final-results}"
export PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-1}"
export PHASE2_GATE_BASELINE_MATCH_SCOPE="${PHASE2_GATE_BASELINE_MATCH_SCOPE:-after-pairs}"
export PHASE2_RUN_KIND="${PHASE2_RUN_KIND:-phase2_function_call_full_matrix_pre_producer}"
export PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT="${PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT:-none}"
export PHASE2_EXPECTED_REASON_MOVEMENT="${PHASE2_EXPECTED_REASON_MOVEMENT:-call_effect_summary_proof/object_evidence_collected/pending_proof}"

exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_pre_producer_32jobs.sh"
