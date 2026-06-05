#!/usr/bin/env bash
# Rebuild all Phase 3 post-fix gate JSON files from existing representative logs.
# This does not run Ghidra analysis; it only reads logs/equivalence_all and artifacts.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

select_python_bin() {
    local candidate
    if [[ -n "${PYTHON_BIN:-}" ]]; then
        echo "$PYTHON_BIN"
        return 0
    fi
    for candidate in         "$SCRIPT_DIR/.venv-pyghidra/bin/python"         "$SCRIPT_DIR/.venv/bin/python"         python3
    do
        if command -v "$candidate" >/dev/null 2>&1 && [[ -x "$(command -v "$candidate")" ]]; then
            echo "$candidate"
            return 0
        fi
    done
    echo python3
}

PYTHON_BIN="$(select_python_bin)"
BASELINE_RAW_DIR="${BASELINE_RAW_DIR:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/raw}"
BASELINE_FUNCTION_CALL_LOG_ROOT="${BASELINE_FUNCTION_CALL_LOG_ROOT:-$BASELINE_RAW_DIR/logs/function_call}"
BASELINE_LOOP_LOG_ROOT="${BASELINE_LOOP_LOG_ROOT:-$BASELINE_RAW_DIR/logs/loop}"
PHASE1_DIR="${PHASE1_DIR:-$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/phase1}"
PHASE1_FUNCTION_CALL_LOG_ROOT="${PHASE1_FUNCTION_CALL_LOG_ROOT:-$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase2_full_current}"
PHASE1_LOOP_LOG_ROOT="${PHASE1_LOOP_LOG_ROOT:-$BASELINE_LOOP_LOG_ROOT}"
PHASE3_REQUIRE_READY="${PHASE3_REQUIRE_READY:-1}"

require_ready_args=()
if [[ "$PHASE3_REQUIRE_READY" != "0" ]]; then
    require_ready_args+=(--require-ready)
fi

manifest_sha256() {
    sha256sum "$1" | awk '{print $1}'
}

run_gate() {
    echo
    echo "============================================================"
    echo "Running: $PYTHON_BIN -m $* ${require_ready_args[*]}"
    echo "============================================================"
    "$PYTHON_BIN" -m "$@" "${require_ready_args[@]}"
}

LANE1_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_return_coverage_lane1_reclassification/return_coverage_lane1_representatives.json"
LANE2_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_return_width_bridge_lane2/return_width_bridge_lane2_representatives.json"
LANE3_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_readonly_identity_lane3/readonly_identity_lane3_representatives.json"
LANE4_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_method_b_closure_lane4/method_b_closure_lane4_representatives.json"
LANE5_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_sat_unsafety_lane5/sat_unsafety_lane5_representatives.json"
LANE6_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_unresolved_expression_lane6/unresolved_expression_lane6_representatives.json"
LANE7_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_solver_rewrite_lane7/solver_rewrite_lane7_representatives.json"
LANE8_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_solver_rewrite_proof_lane8/solver_rewrite_proof_lane8_representatives.json"
LANE9_MANIFEST="$SCRIPT_DIR/artifacts/baselines/observed-v0@0a53352/audit/phase3_solver_timeout_lane9/solver_timeout_lane9_representatives.json"

run_gate scripts.function_tracer_pcode.validation.phase3_return_coverage_lane1     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_coverage_lane1_representatives/phase3_return_coverage_lane1_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_coverage_lane1_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase1-dir "$PHASE1_DIR"     --phase1-current-log-root "function_call=$PHASE1_FUNCTION_CALL_LOG_ROOT"     --phase1-current-log-root "loop=$PHASE1_LOOP_LOG_ROOT"     --phase3-manifest "$LANE1_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE1_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_return_width_bridge_lane2     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_width_bridge_lane2_representatives/phase3_return_width_bridge_lane2_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_return_width_bridge_lane2_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase3-manifest "$LANE2_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE2_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_readonly_identity_lane3     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_readonly_identity_lane3_representatives/phase3_readonly_identity_lane3_gate"     --current-log-root "loop=$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_readonly_identity_lane3_representatives"     --baseline-log-root "loop=$BASELINE_LOOP_LOG_ROOT"     --phase3-manifest "$LANE3_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE3_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_method_b_closure_lane4     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_method_b_closure_lane4_representatives/phase3_method_b_closure_lane4_gate"     --current-log-root "loop=$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_method_b_closure_lane4_representatives"     --baseline-log-root "loop=$BASELINE_LOOP_LOG_ROOT"     --phase3-manifest "$LANE4_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE4_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_sat_unsafety_lane5     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_sat_unsafety_lane5_representatives/phase3_sat_unsafety_lane5_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_sat_unsafety_lane5_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase3-manifest "$LANE5_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE5_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_unresolved_expression_lane6     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_unresolved_expression_lane6_representatives/phase3_unresolved_expression_lane6_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_unresolved_expression_lane6_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase3-manifest "$LANE6_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE6_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_solver_rewrite_lane7     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_solver_rewrite_lane7_representatives/phase3_solver_rewrite_lane7_gate"     --current-log-root "loop=$SCRIPT_DIR/logs/equivalence_all/loop_test_phase3_solver_rewrite_lane7_representatives"     --baseline-log-root "loop=$BASELINE_LOOP_LOG_ROOT"     --phase3-manifest "$LANE7_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE7_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_solver_rewrite_proof_lane8     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_solver_rewrite_proof_lane8_representatives/phase3_solver_rewrite_proof_lane8_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_solver_rewrite_proof_lane8_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase3-manifest "$LANE8_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE8_MANIFEST")"

run_gate scripts.function_tracer_pcode.validation.phase3_solver_timeout_lane9     --gate-stage post-fix     --baseline-raw-dir "$BASELINE_RAW_DIR"     --output-dir "$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_solver_timeout_lane9_representatives/phase3_solver_timeout_lane9_gate"     --current-log-root "function_call=$SCRIPT_DIR/logs/equivalence_all/function_call_test_phase3_solver_timeout_lane9_representatives"     --baseline-log-root "function_call=$BASELINE_FUNCTION_CALL_LOG_ROOT"     --phase3-manifest "$LANE9_MANIFEST"     --phase3-manifest-sha256 "$(manifest_sha256 "$LANE9_MANIFEST")"

echo
PHASE3_INCLUDE_FULL_MATRIX_DELTA_GATES=1 "$SCRIPT_DIR/phase3_validate_all_post_fix_gates.sh"
