#!/usr/bin/env bash
# Risk-stratified Phase 2 final-result movement preflight.
#
# This is a shell-level safety check, not the Phase 2 expected-movement
# validator. It runs the producer flags on return-coverage recovery risk pairs
# selected from existing logs and requires the filtered baseline final result
# to stay unchanged.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"
PYTHON_BIN="${PYTHON_BIN:-python3}"
RISK_CURRENT_LOG_ROOT="${RISK_CURRENT_LOG_ROOT:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_full_current}"
RISK_BASELINE_LOG_ROOT="${RISK_BASELINE_LOG_ROOT:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/raw/logs/function_call}"
export OUTPUT_BASE_DIR="${OUTPUT_BASE_DIR:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_pre_producer_final_result_preflight}"
RISK_PREFLIGHT_MANIFEST="${RISK_PREFLIGHT_MANIFEST:-$OUTPUT_BASE_DIR/risk_preflight_selection_manifest.json}"
mkdir -p "$OUTPUT_BASE_DIR"

if [[ -z "${FUNCTION_CALL_TARGET_SET:-}" || -z "${FUNCTION_CALL_PAIR_FILTER:-}" ]]; then
    RISK_PREFLIGHT_EXPORTS="$(
        "$PYTHON_BIN" -m scripts.function_tracer_pcode.validation.phase2_return_coverage_risk_preflight \
            --current-log-root "$RISK_CURRENT_LOG_ROOT" \
            --baseline-log-root "$RISK_BASELINE_LOG_ROOT" \
            --max-per-stratum "${RISK_PREFLIGHT_MAX_PER_STRATUM:-2}" \
            --max-evidence-only-per-stratum "${RISK_PREFLIGHT_MAX_EVIDENCE_ONLY_PER_STRATUM:-1}" \
            --max-pairs "${RISK_PREFLIGHT_MAX_PAIRS:-24}" \
            --sample-seed "${RISK_PREFLIGHT_SAMPLE_SEED:-0}" \
            --manifest-path "$RISK_PREFLIGHT_MANIFEST"
    )"
    eval "$RISK_PREFLIGHT_EXPORTS"
fi

export FUNCTION_CALL_TARGET_SET="${FUNCTION_CALL_TARGET_SET:-fc_recursive_sum,fc_dispatch_indirect}"
export FUNCTION_CALL_PAIR_FILTER="${FUNCTION_CALL_PAIR_FILTER:-fc_recursive_sum:B3_B7,fc_dispatch_indirect:B1_B2,fc_dispatch_indirect:B3_B4}"
export RISK_PREFLIGHT_MANIFEST
export PARALLEL_JOBS="${PARALLEL_JOBS:-4}"
export VALIDATION_SKIP_COMPLETED="${VALIDATION_SKIP_COMPLETED:-0}"
export VALIDATION_REQUIRE_BASELINE_MATCH="${VALIDATION_REQUIRE_BASELINE_MATCH:-1}"
export VALIDATION_BASELINE_MATCH_SCOPE="${VALIDATION_BASELINE_MATCH_SCOPE:-after-pairs}"
export VALIDATION_BASELINE_MATCH_LEVEL="${VALIDATION_BASELINE_MATCH_LEVEL:-final-results}"
export PHASE2_RUN_EXPECTED_MOVEMENT_GATE="${PHASE2_RUN_EXPECTED_MOVEMENT_GATE:-0}"
export PHASE2_RUN_KIND="${PHASE2_RUN_KIND:-phase2_function_call_pre_producer_final_result_preflight}"
export PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT="${PHASE2_EXPECTED_FINAL_RESULT_MOVEMENT:-none}"
export PHASE2_EXPECTED_REASON_MOVEMENT="${PHASE2_EXPECTED_REASON_MOVEMENT:-preflight-final-result-invariant}"

exec "$SCRIPT_DIR/phase2_run_function_call_full_matrix_pre_producer_32jobs.sh"
