#!/usr/bin/env bash
# Run the Phase 2 producer-validation function_call matrix.
#
# This wrapper intentionally disables completed recovery proofs so the
# equivalence_blocking_unsafety gate can observe the pending proof tuple without
# normal recovery converting completed proofs into final results. Retry phases
# stay enabled because disabling them exposes known false NOT_EQ producer
# counterexamples for same-source pairs.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

export OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_full_pre_producer}"
export VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-0}"
export VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS="${VALIDATION_REQUIRE_PHASE2_OBJECT_KEYS:-1}"
export FUNCTION_CALL_EXTRA_EQUIV_ARGS="${FUNCTION_CALL_EXTRA_EQUIV_ARGS:---no-completed-recovery-proofs}"
export PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-1}"
export PHASE2_RUN_KIND="${PHASE2_RUN_KIND:-phase2_function_call_full_matrix_pre_producer}"
export PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT="${PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT:-none}"
export PHASE2_EXPECTED_REASON_MOVEMENT="${PHASE2_EXPECTED_REASON_MOVEMENT:-call_effect_summary_proof/object_evidence_collected/pending_proof}"

exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_32jobs.sh"
